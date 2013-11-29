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
   Ref_Module              : W_Module_Id;

   --  Modules of "_gnatprove_standard.mlw"

   Main_Module             : W_Module_Id;
   Integer_Module          : W_Module_Id;
   Floating_Module         : W_Module_Id;
   Boolean_Module          : W_Module_Id;
   Array_Modules           : W_Module_Array (1 .. 4);

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

   function E_Module (E : Entity_Id) return W_Module_Id;
   --  this function returns the module where File = No_Name and Name =
   --  Full_Name (E). Memoization may be used. Returns empty when it is called
   --  with a node which is not an entity, and no module is known for this
   --  entity.

   procedure Insert_Extra_Module (N : Node_Id; M : W_Module_Id);
   --  After a call to this procedure, E_Module (N) will return M.

end Why.Atree.Modules;
