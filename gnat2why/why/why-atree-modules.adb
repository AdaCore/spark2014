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

with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Names;      use Why.Gen.Names;

package body Why.Atree.Modules is

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

      Int_Module :=
        New_Module
          (File => Int_File,
           Name => NID ("Int"));
      RealInfix :=
        New_Module
          (File => Real_File,
           Name => NID ("RealInfix"));

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

end Why.Atree.Modules;
