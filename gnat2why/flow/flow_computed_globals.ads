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

--  This package implements writing, reading and computing global
--  contracts.

with Types;                       use Types;

with Common_Containers;           use Common_Containers;
with Ada.Containers.Ordered_Sets;

with Flow_Types;                  use Flow_Types;
with Flow_Refinement;             use Flow_Refinement;
with Flow_Dependency_Maps;        use Flow_Dependency_Maps;

package Flow_Computed_Globals is

   --  -------------------------------------
   --  -- Flow_Computed_Globals Algorithm --
   --  -------------------------------------

   --  This algorithm is applied on a per Compilation Unit basis.

   --  During the first pass:
   --    * For every subprogram in SPARK a GG graph is created. The
   --      graph is then traversed and all global variables are classified
   --      as proof ins, ins and outs. During the traversal we also
   --      classify called subprograms as proof only calls, definite calls
   --      and conditional calls. Lastly we take note of all local
   --      variables. This info is then appended on the ALI file.
   --    * For every subprogram that is NOT in SPARK and does NOT have
   --      a user-provided contract a GG graph is NOT created. However, we
   --      do create GG entries for those subprograms in the ALI file.
   --      Those GG entries mirror the information that (Yannick's)
   --      computed globals store in the ALI file. As a result, all
   --      subprogram calls are considered to be conditional calls and all
   --      writes to variables are considered to be read-writes (pure reads
   --      are also included in the reads of course).
   --    * For every package we gather all know state abstractions and
   --      all their constituents and that info is then appended on the
   --      ALI file.

   --  During the second pass:
   --    * All information stored in the ALI files during the first
   --      pass is read back.
   --    * A Global Graph for the entire compilation unit is created.
   --      This graph contains subprograms and variables only. No
   --      abstract states and packages are present on this graph.
   --      We create 3 vertices per subprogram. These represent the
   --      subprogram's proof inputs, inputs and outputs. For each
   --      variable we create a single vertex that represents the
   --      variable.
   --    * We then draw edges between those vertices based on the GG
   --      info that we read from the ALI files. For subprograms that
   --      are marked as SPARK_Mode Off or that contain illegal SPARK
   --      contracts we use the Get_Globals function instead of the GG
   --      info from the ALI files.
   --    * Lastly we use the compilation unit's Global Graph and
   --      information that we have about state abstractions and their
   --      constituents to return globals relatively to the caller's
   --      scope.

   --  -------------------------------
   --  -- Generated Globals Section --
   --  -------------------------------

   --  The Generated Globals section is located at the end of the ALI file.

   --  All lines introducing information related to the Generated Globals
   --  have the string "GG" appearing in the beginning.

   --  The Generated Globals section holds two kinds of information:

   --  1) The first kind has to do with Abstract States and the
   --     constituents thereof.

   --     Information related to this kind occupy single lines and have
   --     the string "AS" immediately after "GG". Following "AS" comes
   --     the name of the Abstract State and following that are all its
   --     constituents.

   --     Example entries:
   --       GG AS test__state test__constit_1 test__constit_2
   --       GG AS test__state2
   --       GG AS test__state3 test_state2

   --  2) The second kind has to do with subprograms. For subprograms we
   --     store the following:

   --       * the subprogram's name and where the info comes from    (S)
   --       * the global variables read in proof contexts only       (VP)
   --       * the global variables read    (input)                   (VI)
   --       * the global variables written (output)                  (VO)
   --       * the subprograms that are called only in proof contexts (CP)
   --       * the subprograms that are called definitely             (CD)
   --       * the subprograms that are called conditionally          (CC)
   --       * the local variables of the subprogram                  (LV)

   --     For an entry of the second kind to be complete/correct all of the
   --     afformentioned lines must be present (order does not matter).

   --     Example entry:
   --       GG S FA test__proc
   --       GG VP test__proof_var
   --       GG VI test__g test__g2
   --       GG VO test__g
   --       GG CP test__ghost_func_a test__ghost_func_b
   --       GG CD test__proc_2 test__proc__nested_proc
   --       GG CC test__proc_3
   --       GG LV test__proc__nested_proc__v

   ----------------------------------------------------------------------

   type GG_Mode_T is (GG_No_Mode,
                      GG_Read_Mode,
                      GG_Write_Mode);

   type Globals_Origin_T is (UG, FA, XR, NO);
   --  UG = User Globals
   --  FA = Flow Analysis
   --  XR = xref
   --  NO = No Origin (we should never get this)

   type Subprogram_Phase_1_Info is record
      Subprogram        : Entity_Name;
      Globals_Origin    : Globals_Origin_T;

      Inputs_Proof      : Name_Set.Set;
      Inputs            : Name_Set.Set;
      Outputs           : Name_Set.Set;
      Proof_Calls       : Name_Set.Set;
      Definite_Calls    : Name_Set.Set;
      Conditional_Calls : Name_Set.Set;
      Local_Variables   : Name_Set.Set;
   end record;

   Null_Subprogram_Info : constant Subprogram_Phase_1_Info :=
     Subprogram_Phase_1_Info'(Subprogram        => Null_Entity_Name,
                              Globals_Origin    => NO,
                              Inputs_Proof      => Name_Set.Empty_Set,
                              Inputs            => Name_Set.Empty_Set,
                              Outputs           => Name_Set.Empty_Set,
                              Proof_Calls       => Name_Set.Empty_Set,
                              Definite_Calls    => Name_Set.Empty_Set,
                              Conditional_Calls => Name_Set.Empty_Set,
                              Local_Variables   => Name_Set.Empty_Set);

   function Preceeds (A, B : Subprogram_Phase_1_Info) return Boolean
   is (A.Subprogram.all < B.Subprogram.all);

   package Info_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Subprogram_Phase_1_Info,
      "<"          => Preceeds,
      "="          => "=");

   Info_Set : Info_Sets.Set;

   ----------------------------------------------------------------------

   function To_Name (E : Entity_Id) return Entity_Name;
   --  Takes an Entity_Id and returns the corresponding Entity_Name

   function To_Name_Set (S : Node_Sets.Set) return Name_Set.Set;
   --  Takes a set of Node_Ids and returns a set of Entity_Names

   function GG_Mode return GG_Mode_T;
   --  Returns the current mode.

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
   --  returning the most refined view).

   procedure GG_Write_Subprogram_Info (SI : Subprogram_Phase_1_Info)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Records the information we need to later compute globals.
   --  Compute_Globals in Flow.Slice is used to produce the inputs.

   procedure GG_Write_Finalize
   with Pre => GG_Mode = GG_Write_Mode;
   --  Appends all subprogram and package information to the ALI file.

   -------------------------
   -- Reading & Computing --
   -------------------------

   procedure GG_Read (GNAT_Root : Node_Id)
   with Pre  => GG_Mode = GG_No_Mode,
        Post => GG_Mode = GG_Read_Mode;
   --  Reads all ALI files and produces the transitive closure.

   -----------
   -- Query --
   -----------

   function GG_Exist (E : Entity_Id) return Boolean
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns True if generated globals have been computed for the
   --  given entity.

   function GG_Has_Refinement (EN : Entity_Name) return Boolean
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns true if E is a state abstraction whose constituents we
   --  loaded while reading the ali files.

   function GG_Is_Constituent (EN : Entity_Name) return Boolean
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns true if E is a constituent of some state abstraction
   --  that we loaded while reading the ali files.

   function GG_Get_Constituents (EN : Entity_Name) return Name_Set.Set
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns the set of direct constituents of a state abstraction
   --  or an Empty_Set if they do not exist.

   function GG_Enclosing_State (EN : Entity_Name) return Entity_Name
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns the Entity_Name of the directly enclosing state. If one
   --  does not exist it returns Null_Entity_Name.

   function GG_Fully_Refine (EN : Entity_Name) return Name_Set.Set
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
   --  Determines the set of all globals.

   function GG_Get_Proof_Reads
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set of variables read in proof contexts.

   function GG_Get_Reads
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set of variables read.

   function GG_Get_All_Reads
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set of all (proof and ordinary) variables read.

   function GG_Get_Writes
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set of all variables written.

private

   Current_Mode : GG_Mode_T := GG_No_Mode;

   -------------
   -- GG_Mode --
   -------------

   function GG_Mode return GG_Mode_T is (Current_Mode);

end Flow_Computed_Globals;
