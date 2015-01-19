------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - A T R E E - M O D U L E S                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

with SPARK_Definition; use SPARK_Definition;
with Why.Ids;          use Why.Ids;

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

   Int_Module                : W_Module_Id;
   RealInfix                 : W_Module_Id;
   Ref_Module                : W_Module_Id;

   --  basic Why types

   EW_Bool_Type    : W_Type_Id;
   EW_Int_Type     : W_Type_Id;
   EW_Fixed_Type   : W_Type_Id;
   EW_Private_Type : W_Type_Id;
   EW_Prop_Type    : W_Type_Id;
   EW_Real_Type    : W_Type_Id;
   EW_Unit_Type    : W_Type_Id;

   --  Modules of "_gnatprove_standard.mlw"

   Main_Module               : W_Module_Id;
   Integer_Module            : W_Module_Id;
   Int_Power_Module          : W_Module_Id;
   Int_Div_Module            : W_Module_Id;
   Int_Bit_Module            : W_Module_Id;
   Int_Abs_Module            : W_Module_Id;
   Int_Minmax_Module         : W_Module_Id;
   Floating_Module           : W_Module_Id;
   Boolean_Module            : W_Module_Id;
   Array_Modules             : W_Module_Array (1 .. Max_Array_Dimensions);

   --  Modules of file "ada__model.mlw"

   Static_Discrete           : W_Module_Id;
   Static_Modular            : W_Module_Id;
   Dynamic_Discrete          : W_Module_Id;
   Dynamic_Modular           : W_Module_Id;
   Static_Fixed_Point        : W_Module_Id;
   Dynamic_Fixed_Point       : W_Module_Id;
   Static_Floating_Point     : W_Module_Id;
   Dynamic_Floating_Point    : W_Module_Id;

   Constr_Arrays             : W_Module_Array (1 .. Max_Array_Dimensions);
   Unconstr_Arrays           : W_Module_Array (1 .. Max_Array_Dimensions);
   Array_Comparison_Ax       : W_Module_Id;
   Standard_Array_Logical_Ax : W_Module_Id;
   Subtype_Array_Logical_Ax  : W_Module_Id;

   --  Identifiers of the Main module

   String_Image_Type         : W_Type_Id;
   Type_Of_Heap              : W_Type_Id;
   Havoc_Fun                 : W_Identifier_Id;
   Ignore_Id                 : W_Identifier_Id;
   Bool_Not                  : W_Identifier_Id;
   --  builtin unary minus

   Int_Unary_Minus           : W_Identifier_Id;
   Fixed_Unary_Minus         : W_Identifier_Id;
   Real_Unary_Minus          : W_Identifier_Id;

   --  builtin infix symbols

   Why_Eq                    : W_Identifier_Id;
   Why_Neq                   : W_Identifier_Id;
   Int_Infix_Add             : W_Identifier_Id;
   Int_Infix_Subtr           : W_Identifier_Id;
   Int_Infix_Mult            : W_Identifier_Id;
   Int_Infix_Le              : W_Identifier_Id;
   Int_Infix_Ge              : W_Identifier_Id;
   Int_Infix_Gt              : W_Identifier_Id;
   Int_Infix_Lt              : W_Identifier_Id;

   Fixed_Infix_Add           : W_Identifier_Id;
   Fixed_Infix_Subtr         : W_Identifier_Id;
   Fixed_Infix_Mult          : W_Identifier_Id;

   Real_Infix_Add            : W_Identifier_Id;
   Real_Infix_Subtr          : W_Identifier_Id;
   Real_Infix_Mult           : W_Identifier_Id;
   Real_Infix_Lt             : W_Identifier_Id;
   Real_Infix_Le             : W_Identifier_Id;
   Real_Infix_Gt             : W_Identifier_Id;
   Real_Infix_Ge             : W_Identifier_Id;

   --  Identifiers of the Integer module

   Integer_Bitwise_And       : W_Identifier_Id;
   Integer_Bitwise_Or        : W_Identifier_Id;
   Integer_Bitwise_Xor       : W_Identifier_Id;
   Integer_Div               : W_Identifier_Id;
   Euclid_Div                : W_Identifier_Id;
   Integer_Rem               : W_Identifier_Id;
   Integer_Mod               : W_Identifier_Id;
   Integer_Power             : W_Identifier_Id;
   Integer_Math_Mod          : W_Identifier_Id;
   Integer_Max               : W_Identifier_Id;
   Integer_Min               : W_Identifier_Id;
   Integer_Abs               : W_Identifier_Id;

   Int_Bool_Eq               : W_Identifier_Id;
   Int_Bool_Lt               : W_Identifier_Id;
   Int_Bool_Le               : W_Identifier_Id;
   Int_Bool_Ne               : W_Identifier_Id;
   Int_Bool_Gt               : W_Identifier_Id;
   Int_Bool_Ge               : W_Identifier_Id;

   Floating_Div_Real         : W_Identifier_Id;
   Floating_Abs_Real         : W_Identifier_Id;
   Floating_Ceil             : W_Identifier_Id;
   Floating_Floor            : W_Identifier_Id;
   Floating_Power            : W_Identifier_Id;
   Floating_Real_Of_Int      : W_Identifier_Id;
   Floating_Round            : W_Identifier_Id;
   Floating_Truncate         : W_Identifier_Id;
   Floating_Max              : W_Identifier_Id;
   Floating_Min              : W_Identifier_Id;
   Floating_Round_Single     : W_Identifier_Id;
   Floating_Round_Double     : W_Identifier_Id;

   Real_Bool_Eq               : W_Identifier_Id;
   Real_Bool_Lt               : W_Identifier_Id;
   Real_Bool_Le               : W_Identifier_Id;
   Real_Bool_Ne               : W_Identifier_Id;
   Real_Bool_Gt               : W_Identifier_Id;
   Real_Bool_Ge               : W_Identifier_Id;

   Bool_Bool_Eq               : W_Identifier_Id;
   Bool_Bool_Lt               : W_Identifier_Id;
   Bool_Bool_Le               : W_Identifier_Id;
   Bool_Bool_Ne               : W_Identifier_Id;
   Bool_Bool_Gt               : W_Identifier_Id;
   Bool_Bool_Ge               : W_Identifier_Id;

   To_String_Id               : W_Identifier_Id;
   Of_String_Id               : W_Identifier_Id;

   --  Other identifiers

   Old_Tag                   : Name_Id;
   Return_Exc                : W_Name_Id;

   procedure Initialize;
   --  Call this procedure before using any of the entities in this package.

   function E_Module (E : Entity_Id) return W_Module_Id;
   --  this function returns the module where File = No_Name and Name =
   --  Full_Name (E). Memoization may be used. Returns empty when it is called
   --  with a node which is not an entity, and no module is known for this
   --  entity.

   function E_Axiom_Module (E : Entity_Id) return W_Module_Id;

   procedure Insert_Extra_Module (N : Node_Id; M : W_Module_Id);
   --  After a call to this procedure, E_Module (N) will return M.

end Why.Atree.Modules;
