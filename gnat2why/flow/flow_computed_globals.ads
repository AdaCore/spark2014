------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--               F L O W . C O M P U T E D _ G L O B A L S                  --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--               Copyright (C) 2014, Altran UK Limited                 --
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

with Types;                use Types;

with Common_Containers;    use Common_Containers;

with Flow_Types;           use Flow_Types;
with Flow_Refinement;      use Flow_Refinement;
with Flow_Dependency_Maps; use Flow_Dependency_Maps;

package Flow_Computed_Globals is

   type GG_Mode_T is (GG_No_Mode,
                      GG_Read_Mode,
                      GG_Write_Mode);

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

   procedure GG_Write_Subprogram_Info
     (E                 : Entity_Id;
      Inputs_Proof      : Node_Sets.Set;
      Inputs            : Node_Sets.Set;
      Outputs           : Node_Sets.Set;
      Proof_Calls       : Node_Sets.Set;
      Definite_Calls    : Node_Sets.Set;
      Conditional_Calls : Node_Sets.Set;
      Local_Variables   : Node_Sets.Set)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Records the information we need to later compute globals.
   --  Compute_Globals in Flow.Slice is used to produce the inputs.

   procedure GG_Write_Finalize
   with Pre  => GG_Mode = GG_Write_Mode;
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
   --  Returns true if flow globals have been computed for the given
   --  entity.

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
