------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--               F L O W . C O M P U T E D _ G L O B A L S                  --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--               Copyright (C) 2015, Altran UK Limited                      --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

--  This package implements writing, reading and computing global contracts

with Types;                       use Types;

with Common_Containers;           use Common_Containers;
with Ada.Containers.Ordered_Sets;

with Flow_Types;                  use Flow_Types;
with Flow_Refinement;             use Flow_Refinement;
with Flow_Dependency_Maps;        use Flow_Dependency_Maps;

package Flow_Generated_Globals is

   --  -------------------------------------
   --  -- Flow_Generated_Globals Algorithm --
   --  -------------------------------------

   --  This algorithm is applied to individual compilation units
   --
   --  During the first pass:
   --
   --    * For every subprogram and task in SPARK a GG graph is created. The
   --      graph is then traversed to classify global variables as proof ins,
   --      ins and outs, and called subprograms as proof only calls, definite
   --      calls and conditional calls. Also we take note of all local
   --      variables. This info is then stored in the ALI file.
   --
   --    * For every subprogram and task that is NOT in SPARK and does NOT have
   --      a user-provided contract only GG entries and not a GG graph is
   --      created and stored in the ALI file. Those GG entries mirror the
   --      information that (Yannick's) computed globals store in the ALI file.
   --      As a result, all subprogram calls are considered to be conditional
   --      calls and all writes to variables are considered to be read-writes
   --      (pure reads are also included in the reads of course).
   --
   --    * For every package all known state abstractions and all their
   --      constituents are collected and this info is stored in the ALI file.
   --
   --  During the second pass:
   --
   --    * All information stored in the ALI files during the first pass is
   --      read back.
   --
   --    * A Global Graph for the entire compilation unit is created. This
   --      graph contains only subprograms, tasks and variables; it does not
   --      contain abstract states and packages. There are 3 vertices per
   --      subprogram/task that represent the subprogram's proof inputs, inputs
   --      and outputs. Each variable is represented by a vertex.
   --
   --    * We then draw edges between those vertices based on the GG info that
   --      we read from the ALI files. For subprograms that are marked as
   --      SPARK_Mode Off or that contain illegal SPARK constructs we use the
   --      Get_Globals function instead of the GG info from the ALI files.
   --
   --    * Lastly we use the compilation unit's Global Graph and information
   --      that we have about state abstractions and their constituents to
   --      return globals relatively to the caller's scope.

   --  -------------------------------
   --  -- Generated Globals Section --
   --  -------------------------------

   --  The Generated Globals section is located at the end of the ALI file
   --
   --  All lines with information related to the Generated Globals start with a
   --  "GG" string.
   --
   --  The Generated Globals section stores three kinds of information:
   --
   --  1) The first kind is related to Abstract States and their constituents
   --
   --     This information is stored in single lines that start with "GG"
   --     followed by "AS"; then comes the name of the Abstract State and then
   --     the names of its constituents.
   --
   --     Examples:
   --       GG AS test__state test__constit_1 test__constit_2
   --       GG AS test__state2
   --       GG AS test__state3 test_state2
   --
   --  2) The second kind is related to subprograms, tasks and entries. For
   --     these we store the names of:
   --
   --       * subprogram/task/entry together with the origin of the entry
   --         (see Globals_Origin_T)                             (S/T/E)
   --       * global variables read in proof contexts only       (VP)
   --       * global variables read    (input)                   (VI)
   --       * global variables written (output)                  (VO)
   --       * subprograms that are called only in proof contexts (CP)
   --       * subprograms that are called definitely             (CD)
   --       * subprograms that are called conditionally          (CC)
   --       * local variables of the subprogram                  (LV)
   --       * local subprograms of the subprogram                (LS)

   --     For an entry of the second kind to be complete/correct all of the
   --     afformentioned lines must be present (order does not matter).

   --     Examples:
   --       GG S FA test__proc
   --       GG VP test__proof_var
   --       GG VI test__g test__g2
   --       GG VO test__g
   --       GG CP test__ghost_func_a test__ghost_func_b
   --       GG CD test__proc_2 test__proc__nested_proc
   --       GG CC test__proc_3
   --       GG LV test__proc__nested_proc__v
   --       GG LS test__proc__nested_proc__nested_proc
   --
   --  3) The third kind is related to volatile variables and external state
   --     abstractions.
   --
   --     There are at most 4 lines in the ALI file; one line for each of the
   --     property, with names of the variables and external state
   --     abstractions:
   --
   --       * Async_Writers    (AW)
   --       * Async_Readers    (AR)
   --       * Effective_Reads  (ER)
   --       * Effective_Writes (EW)
   --
   --     Note here that names appearing on ER line have to also appear on the
   --     AW line; the same holds for EW and AR.
   --
   --     Examples:
   --     GG AW test__fully_vol test__vol_er2 test__ext_state
   --     GG AR test__fully_vol test__vol_ew3
   --     GG ER test__fully_vol test__vol_er2
   --     GG EW test__fully_vol test__vol_ew3

   ----------------------------------------------------------------------

   type GG_Mode_T is (GG_No_Mode,
                      GG_Read_Mode,
                      GG_Write_Mode);

   type Globals_Origin_T is (UG, FA, XR);
   --  UG = User Globals
   --  FA = Flow Analysis
   --  XR = xref

   type Info_Kind is (S_Kind, T_Kind, E_Kind);
   --  S_Kind = Subprogram
   --  T_Kind = Task
   --  E_Kind = Entry

   type Subprogram_Phase_1_Info is record
      Name              : Entity_Name;
      Kind              : Info_Kind;
      Globals_Origin    : Globals_Origin_T;
      Inputs_Proof      : Name_Sets.Set;
      Inputs            : Name_Sets.Set;
      Outputs           : Name_Sets.Set;
      Proof_Calls       : Name_Sets.Set;
      Definite_Calls    : Name_Sets.Set;
      Conditional_Calls : Name_Sets.Set;
      Local_Variables   : Name_Sets.Set;
      Local_Subprograms : Name_Sets.Set;
   end record;

   function Preceeds (A, B : Subprogram_Phase_1_Info) return Boolean is
     (A.Name < B.Name);

   package Subprogram_Info_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Subprogram_Phase_1_Info,
      "<"          => Preceeds,
      "="          => "=");
   --  ??? Ordered sets seem to be faster here than hashed sets

   Subprogram_Info_Set : Subprogram_Info_Sets.Set :=
     Subprogram_Info_Sets.Empty_Set;
   --  Information about subprograms from the "generated globals" algorithm

   Nonblocking_Subprograms_Set : Name_Sets.Set := Name_Sets.Empty_Set;
   --  Subprograms, entries and tasks that do not contain potentially blocking
   --  statements (but still may call another blocking subprogram).

   ----------------------------------------------------------------------

   function To_Name_Set (S : Node_Sets.Set) return Name_Sets.Set;
   --  Takes a set of Node_Ids and returns a set of Entity_Names

   function GG_Mode return GG_Mode_T;
   --  Returns the current mode

   -------------
   -- Writing --
   -------------

   procedure GG_Write_Initialize
   with Pre  => GG_Mode = GG_No_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Must be called before the first call to
   --  GG_Write_Subprogram_Info and GG_Write_Package_Info.

   procedure GG_Write_Package_Info (DM : Dependency_Maps.Map)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Records information related to state abstractions and the
   --  refinements thereof. This will later be used to return the
   --  appropriate view depending on the caller (as opposed to always
   --  returning the most refined view). It also stores information
   --  related to external states.

   procedure GG_Write_Subprogram_Info (SI : Subprogram_Phase_1_Info)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Records the information we need to later compute globals.
   --  Compute_Globals in Flow.Slice is used to produce the inputs.
   --  It also stores information related to volatiles and possibly blocking
   --  property.

   procedure GG_Write_Finalize
   with Pre => GG_Mode = GG_Write_Mode;
   --  Appends all collected information to the ALI file

   -------------------------
   -- Reading & Computing --
   -------------------------

   procedure GG_Read (GNAT_Root : Node_Id)
   with Pre  => GG_Mode = GG_No_Mode,
        Post => GG_Mode = GG_Read_Mode;
   --  Reads all ALI files and produces the transitive closure

   --------------
   -- Querying --
   --------------

   function GG_Has_Been_Generated return Boolean;
   --  Checks if the Globals Graph has been generated
   --  @return True iff the Globals Graph has been generated

   function GG_Exist (E : Entity_Id) return Boolean
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns True if generated globals have been computed for the
   --  given entity.

   function GG_Has_Refinement (EN : Entity_Name) return Boolean
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns true if E is a state abstraction whose constituents we
   --  loaded while reading the ALI files.

   function GG_Is_Constituent (EN : Entity_Name) return Boolean
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns true if E is a constituent of some state abstraction
   --  that we loaded while reading the ALI files.

   function GG_Get_Constituents (EN : Entity_Name) return Name_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns the set of direct constituents of a state abstraction
   --  or an Empty_Set if they do not exist.

   function GG_Enclosing_State (EN : Entity_Name) return Entity_Name
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns the Entity_Name of the directly enclosing state. If one
   --  does not exist it returns Null_Entity_Name.

   function GG_Fully_Refine (EN : Entity_Name) return Name_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Has_Refinement (EN);
   --  Returns the most refined constituents of state abstraction EN

   procedure GG_Get_Globals (E           : Entity_Id;
                             S           : Flow_Scope;
                             Proof_Reads : out Flow_Id_Sets.Set;
                             Reads       : out Flow_Id_Sets.Set;
                             Writes      : out Flow_Id_Sets.Set)
   with Pre  => GG_Mode = GG_Read_Mode and then
                GG_Exist (E),
        Post => GG_Mode = GG_Read_Mode;
   --  Determines the set of all globals

   function GG_Get_Proof_Reads
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set of variables read in proof contexts

   function GG_Get_Reads
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set of variables read

   function GG_Get_All_Reads
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set of all (proof and ordinary) variables read

   function GG_Get_Writes
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set of all variables written

   function GG_Get_All_State_Abstractions return Name_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode;
   --  @return a set of Entity_Names with all the state abstractions
   --    that the Generated Globals know of.

   function GG_Is_Volatile (EN : Entity_Name) return Boolean
   with Pre => GG_Has_Been_Generated;
   --  @param EN is the entity name that we check for being volatile
   --  @return True iff EN is volatile.

   function GG_Has_Async_Writers (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Async_Writers'Result
                 then GG_Is_Volatile (EN));
   --  @param EN is the entity name that we check for having Async_Writers
   --  @return True iff EN has Async_Writers set.

   function GG_Has_Async_Readers (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Async_Readers'Result
                 then GG_Is_Volatile (EN));
   --  @param EN is the entity name that we check for having Async_Readers
   --  @return True iff EN has Async_Readers set.

   function GG_Has_Effective_Reads (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Effective_Reads'Result
                 then GG_Has_Async_Writers (EN));
   --  @param EN is the entity name that we check for having Effective_Reads
   --  @return True iff EN has Effective_Reads set.

   function GG_Has_Effective_Writes (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Effective_Writes'Result
                 then GG_Has_Async_Readers (EN));
   --  @param EN is the entity name that we check for having Effective_Writes
   --  @return True iff EN has Effective_Writes set.

private

   Current_Mode : GG_Mode_T := GG_No_Mode;

   GG_Generated : Boolean   := False;
   --  Set to True by GG_Read once the Global Graph has been generated

   -------------
   -- GG_Mode --
   -------------

   function GG_Mode return GG_Mode_T is (Current_Mode);

   ---------------------------
   -- GG_Has_Been_Generated --
   ---------------------------

   function GG_Has_Been_Generated return Boolean is (GG_Generated);
   --  @return True iff the Global Graph has been generated

end Flow_Generated_Globals;
