------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - A T R E E - M O D U L E S                   --
--                                                                          --
--                                 S p e c                                  --
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

with Why.Ids; use Why.Ids;

package Why.Atree.Modules is
   --  This package helps with Why modules. Today, it is only a list of
   --  predefined modules and Why files.

   ---------------------------
   --  Predefined Why Files --
   ---------------------------

   Int_File                : Name_Id;
   Real_File               : Name_Id;
   Ref_File                : Name_Id;
   Gnatprove_Standard_File : Name_Id;
   Ada_Model_File          : Name_Id;

   -----------------------------
   --  Predefined Why modules --
   -----------------------------

   --  the Why standard library

   Int_Module              : W_Module_Id;
   RealInfix               : W_Module_Id;

   --  Modules of file "ada__model.mlw"

   Static_Discrete         : W_Module_Id;
   Static_Modular          : W_Module_Id;
   Dynamic_Discrete        : W_Module_Id;
   Dynamic_Modular         : W_Module_Id;
   Static_Floating_Point   : W_Module_Id;
   Dynamic_Floating_Point  : W_Module_Id;

   Constr_Arrays           : W_Module_Array (1 .. 4);
   Unconstr_Arrays         : W_Module_Array (1 .. 4);

   procedure Initialize;
   --  Call this procedure before using any of the entities in this package.

end Why.Atree.Modules;
