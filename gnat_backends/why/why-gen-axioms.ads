------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       W H Y - G E N - A X I O M S                        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Why.Ids;         use Why.Ids;
with Why.Types;       use Why.Types;
with Why.Sinfo;       use Why.Sinfo;

package Why.Gen.Axioms is
   --  This package provides facilities to generate some standard axioms

   procedure Define_Range_Axiom
     (Theory     : W_Theory_Declaration_Id;
      Type_Name  : W_Identifier_Id;
      Conversion : W_Identifier_Id);
   --  Define a range axiom; it asserts the given abstract type stays in the
   --  range of its base primitive type. The axiom is of the form:
   --
   --  axiom <type_name>___range :
   --   forall x : <type_name>.
   --    <type_name>___in_range (<conversion> (x))

   procedure Define_Coerce_Axiom
     (Theory       : W_Theory_Declaration_Id;
      Type_Name    : W_Identifier_Id;
      Base_Type    : W_Primitive_Type_Id;
      From         : W_Identifier_Id;
      To           : W_Identifier_Id;
      Hypothesis   : W_Pred_Id := Why_Empty;
      Modulus      : W_Term_OId := Why_Empty);

   procedure Define_Coerce_Axiom
     (Theory    : W_Theory_Declaration_Id;
      Type_Name : W_Identifier_Id;
      Base_Type : EW_Scalar;
      Modulus   : W_Term_OId := Why_Empty);
   --  Define a coerce axiom; it asserts that conversion from the base
   --  primitive type then back to the original type is the identity
   --  (as long as we are in the type range). The axiom is of the
   --  form:
   --
   --  axiom <type_name>___coerce :
   --   forall x : <base_type>.
   --    <type_name>___in_range (x) ->
   --     <to_base_type> (<from_base_type> (x)) = x % modulus

   procedure Define_Unicity_Axiom
     (Theory     : W_Theory_Declaration_Id;
      Axiom_Name : W_Identifier_Id;
      Var_Type   : W_Primitive_Type_Id;
      Conversion : W_Identifier_Id);

   procedure Define_Unicity_Axiom
     (Theory    : W_Theory_Declaration_Id;
      Type_Name : W_Identifier_Id;
      Base_Type : W_Identifier_Id);

   procedure Define_Unicity_Axiom
     (Theory    : W_Theory_Declaration_Id;
      Type_Name : W_Identifier_Id;
      Base_Type : EW_Scalar);
   --  Define a unicity axiom; it asserts that if two object of the
   --  given type convert to the same object on its base type, then
   --  they are equal. The axiom is of the form:
   --
   --  axiom standard__integer___unicity :
   --   forall x, y : <type_name>.
   --    <to_base_type> (x) = <to_base_type> (y) -> x = y

end Why.Gen.Axioms;
