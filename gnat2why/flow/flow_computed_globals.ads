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

--  This package implements writing and reading (and computing) global
--  contracts.

with Types;             use Types;

with Common_Containers; use Common_Containers;

with Flow_Types;        use Flow_Types;

package Flow_Computed_Globals is

   type GG_Mode_T is (GG_No_Mode,
                      GG_Read_Mode,
                      GG_Write_Mode);

   function GG_Mode return GG_Mode_T;
   --  Returns the current mode.

   ---------------
   --  Writing  --
   ---------------

   procedure GG_Write_Initialize
   with Pre  => GG_Mode = GG_No_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Must be called before the first call to GG_Write_Subprogram_Info.

   procedure GG_Write_Subprogram_Info
     (E                 : Entity_Id;
      Inputs_Proof      : Node_Sets.Set;
      Inputs            : Node_Sets.Set;
      Outputs           : Node_Sets.Set;
      Proof_Calls       : Node_Sets.Set;
      Definite_Calls    : Node_Sets.Set;
      Conditional_Calls : Node_Sets.Set)
   with Pre  => GG_Mode = GG_Write_Mode,
        Post => GG_Mode = GG_Write_Mode;
   --  Records the information we need to later compute globals.
   --  Compute_Globals in Flow.Slice is used to produce the inputs.

   procedure GG_Write_Finalize
   with Pre  => GG_Mode = GG_Write_Mode;
   --  Appends all subprogram and package information to the ALI file.

   --------------------------
   --  Reading & Computing --
   --------------------------

   procedure GG_Read
   with Pre  => GG_Mode = GG_No_Mode,
        Post => GG_Mode = GG_Read_Mode;
   --  Reads all ALI files and produces the transitive closure.

   -------------
   --  Query  --
   -------------

   function GG_Exist (E : Entity_Id) return Boolean
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns true if flow globals have been computed for the given
   --  entity.

   procedure GG_Get_Globals (E           : Entity_Id;
                             Proof_Reads : out Flow_Id_Sets.Set;
                             Reads       : out Flow_Id_Sets.Set;
                             Writes      : out Flow_Id_Sets.Set)
   with Pre  => GG_Mode = GG_Read_Mode and then
                GG_Exist (E),
        Post => GG_Mode = GG_Read_Mode;
   --  Determines the set of all globals.

   function GG_Get_Proof_Reads (E : Entity_Id) return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set of variables read in proof contexts.

   function GG_Get_Reads (E : Entity_Id) return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set of variables read.

   function GG_Get_All_Reads (E : Entity_Id) return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set all (proof and ordinary) variables read.

   function GG_Get_Writes (E : Entity_Id) return Flow_Id_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Exist (E);
   --  Returns the set all variables written.

private

   Current_Mode : GG_Mode_T := GG_No_Mode;

   -------------
   -- GG_Mode --
   -------------

   function GG_Mode return GG_Mode_T is (Current_Mode);

end Flow_Computed_Globals;
