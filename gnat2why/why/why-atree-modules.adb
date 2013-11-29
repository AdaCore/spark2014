------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - A T R E E - M O D U L E S                   --
--                                                                          --
--                                 B o d Y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Atree;              use Atree;
with Sinfo;              use Sinfo;

with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Names;      use Why.Gen.Names;

with Gnat2Why.Nodes;     use Gnat2Why.Nodes;

package body Why.Atree.Modules is

   Entity_Modules : Ada_To_Why.Map := Ada_To_Why.Empty_Map;
   --------------
   -- E_Module --
   --------------

   function E_Module (E : Entity_Id) return W_Module_Id is
      use Ada_To_Why;
      C : constant Cursor := Entity_Modules.Find (E);
   begin
      if Has_Element (C) then
         return W_Module_Id (Element (C));
      elsif Nkind (E) in N_Entity then
         declare
            M : constant W_Module_Id :=
              New_Module (File => No_Name, Name => NID (Full_Name (E)));
         begin
            Entity_Modules.Insert (E, Why_Node_Id (M));
            return M;
         end;
      else
         return Why_Empty;
      end if;
   end E_Module;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin

      --  initialize files first

      Int_File := NID ("int");
      Real_File := NID ("real");
      Ref_File := NID ("ref");
      Gnatprove_Standard_File := NID ("_gnatprove_standard");
      Ada_Model_File := NID ("ada__model");

      --  modules of the Why standard library

      Int_Module := New_Module (File => Int_File, Name => NID ("Int"));
      RealInfix := New_Module (File => Real_File, Name => NID ("RealInfix"));
      Ref_Module := New_Module (File => Ref_File, Name => NID ("Ref"));

      --  modules of "_gnatprove_standard.mlw" file

      Main_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Main"));
      Integer_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Integer"));
      Floating_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Floating"));
      Boolean_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Boolean"));

      Array_Modules :=
        (1 =>
           New_Module
             (File => Gnatprove_Standard_File,
              Name => NID ("Array__1")),
         2 =>
           New_Module
             (File => Gnatprove_Standard_File,
              Name => NID ("Array__2")),
         3 =>
           New_Module
             (File => Gnatprove_Standard_File,
              Name => NID ("Array__3")),
         4 =>
           New_Module
             (File => Gnatprove_Standard_File,
              Name => NID ("Array__4")));

      --  modules of "ada__model" file

      Static_Modular :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular"));
      Static_Discrete :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Discrete"));
      Dynamic_Modular :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Modular"));
      Dynamic_Discrete :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Discrete"));
      Static_Floating_Point :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Floating_Point"));
      Dynamic_Floating_Point :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Floating_Point"));

      Constr_Arrays :=
        (1 => New_Module (File => Ada_Model_File,
                          Name => NID ("Constr_Array")),
         2 => New_Module (File => Ada_Model_File,
                          Name => NID ("Constr_Array_2")),
         3 => New_Module (File => Ada_Model_File,
                          Name => NID ("Constr_Array_3")),
         4 => New_Module (File => Ada_Model_File,
                          Name => NID ("Constr_Array_4")));
      Unconstr_Arrays :=
        (1 => New_Module (File => Ada_Model_File,
                          Name => NID ("Unconstr_Array")),
         2 => New_Module (File => Ada_Model_File,
                          Name => NID ("Unconstr_Array_2")),
         3 => New_Module (File => Ada_Model_File,
                          Name => NID ("Unconstr_Array_3")),
         4 => New_Module (File => Ada_Model_File,
                          Name => NID ("Unconstr_Array_4")));

   end Initialize;

   -------------------------
   -- Insert_Extra_Module --
   -------------------------

   procedure Insert_Extra_Module (N : Node_Id; M : W_Module_Id) is
   begin
      Entity_Modules.Insert (N, Why_Node_Id (M));
   end Insert_Extra_Module;
end Why.Atree.Modules;
