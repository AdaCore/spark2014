------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--               F L O W . C O M P U T E D _ G L O B A L S                  --
--                                                                          --
--                                B o d y                                   --
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

--  with Osint.C; use Osint.C;

package body Flow_Computed_Globals is

   use type Flow_Id_Sets.Set;

   --  type Subprogram_Phase_1_Info is record
   --     Subprogram        : Entity_Name;

   --     Inputs_Proof      : Name_Set.Set;
   --     Inputs            : Name_Set.Set;
   --     Outputs           : Name_Set.Set;
   --     Proof_Calls       : Name_Set.Set;
   --     Definite_Calls    : Name_Set.Set;
   --     Conditional_Calls : Name_Set.Set;
   --  end record;

   -------------------------
   -- GG_Write_Initialize --
   -------------------------

   procedure GG_Write_Initialize
   is
   begin
      --  Open_Output_Library_Info;
      Current_Mode := GG_Write_Mode;
   end GG_Write_Initialize;

   ------------------------------
   -- GG_Write_Subprogram_Info --
   ------------------------------

   procedure GG_Write_Subprogram_Info
     (E                 : Entity_Id;
      Inputs_Proof      : Node_Sets.Set;
      Inputs            : Node_Sets.Set;
      Outputs           : Node_Sets.Set;
      Proof_Calls       : Node_Sets.Set;
      Definite_Calls    : Node_Sets.Set;
      Conditional_Calls : Node_Sets.Set)
   is
   begin
      null;
   end GG_Write_Subprogram_Info;

   -----------------------
   -- GG_Write_Finalize --
   -----------------------

   procedure GG_Write_Finalize
   is
   begin
      --  Close_Output_Library_Info;
      Current_Mode := GG_No_Mode;
   end GG_Write_Finalize;

   -------------
   -- GG_Read --
   -------------

   procedure GG_Read
   is
   begin
      Current_Mode := GG_Read_Mode;
   end GG_Read;

   --------------
   -- GG_Exist --
   --------------

   function GG_Exist (E : Entity_Id) return Boolean
   is
      pragma Unreferenced (E);
   begin
      return False;
   end GG_Exist;

   --------------------
   -- GG_Get_Globals --
   --------------------

   procedure GG_Get_Globals (E           : Entity_Id;
                             Proof_Reads : out Flow_Id_Sets.Set;
                             Reads       : out Flow_Id_Sets.Set;
                             Writes      : out Flow_Id_Sets.Set)
   is
      pragma Unreferenced (E);
   begin
      Proof_Reads := Flow_Id_Sets.Empty_Set;
      Reads       := Flow_Id_Sets.Empty_Set;
      Writes      := Flow_Id_Sets.Empty_Set;
   end GG_Get_Globals;

   ------------------------
   -- GG_Get_Proof_Reads --
   ------------------------

   function GG_Get_Proof_Reads (E : Entity_Id) return Flow_Id_Sets.Set
   is
      pragma Unreferenced (E);
   begin
      return Flow_Id_Sets.Empty_Set;
   end GG_Get_Proof_Reads;

   ------------------
   -- GG_Get_Reads --
   ------------------

   function GG_Get_Reads (E : Entity_Id) return Flow_Id_Sets.Set
   is
      pragma Unreferenced (E);
   begin
      return Flow_Id_Sets.Empty_Set;
   end GG_Get_Reads;

   ----------------------
   -- GG_Get_All_Reads --
   ----------------------

   function GG_Get_All_Reads (E : Entity_Id) return Flow_Id_Sets.Set
   is
   begin
      return GG_Get_Proof_Reads (E) or GG_Get_Reads (E);
   end GG_Get_All_Reads;

   -------------------
   -- GG_Get_Writes --
   -------------------

   function GG_Get_Writes (E : Entity_Id) return Flow_Id_Sets.Set
   is
      pragma Unreferenced (E);
   begin
      return Flow_Id_Sets.Empty_Set;
   end GG_Get_Writes;

end Flow_Computed_Globals;
