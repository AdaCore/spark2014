------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    W H Y - G E N - H A R D C O D E D                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2020-2024, AdaCore                     --
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

with Gnat2Why.Util;        use Gnat2Why.Util;
with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Util;           use SPARK_Util;
with SPARK_Util.Hardcoded; use SPARK_Util.Hardcoded;
with Types;                use Types;
with Why.Gen.Terms;        use Why.Gen.Terms;
with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;

package Why.Gen.Hardcoded is

   function Dynamic_Property_For_Hardcoded_Type
     (E    : Type_Kind_Id;
      Expr : W_Term_Id)
      return W_Pred_Id
   with Pre => Is_Hardcoded_Entity (E),
     Post => (if Dynamic_Property_For_Hardcoded_Type'Result /= True_Pred
              then Hardcoded_Type_Needs_Dynamic_Property (E));
   --  Some hardcoded types have a dynamic property that should be carried
   --  around.

   function Hardcoded_Type_Needs_Dynamic_Property
     (E : Type_Kind_Id) return Boolean
     with Pre => Is_Hardcoded_Entity (E);

   procedure Emit_Hardcoded_Type_Declaration (Th : Theory_UC; E : Entity_Id)
   with
     Pre => Is_Type (E) and then Is_Hardcoded_Entity (E);
   --  Emit declaration of a Why3 type whose representative type is
   --  hardcoded.
   --  @param Theory the theory where the declaration will be emitted.
   --  @param Entity corresponding to the type declaration.

   function Hardcoded_Constant_Value (E : E_Constant_Id) return W_Term_Id with
     Pre => Is_Hardcoded_Entity (E);
   --  Get the value of a hardcoded constant

   function Hardcoded_Equality_Symbol
     (Typ    : Entity_Id;
      Domain : EW_Domain)
      return W_Identifier_Id
   with
     Pre => Is_Type (Typ) and then Is_Hardcoded_Entity (Typ);
   --  Return the equality symbol for type Typ

   function Is_Hardcoded_Comparison (Subp : Entity_Id) return Boolean;
   --  Return True if Subp is a comparison operator and gains to be translated
   --  in the predicate domain.

   function Is_Hardcoded_Operation (Op          : N_Binary_Op;
                                    Left, Right : Type_Kind_Id)
                                    return Boolean;
   --  Return True if the binary operator is hardcoded.

   function Transform_Hardcoded_Function_Call
     (Subp     : Entity_Id;
      Args     : W_Expr_Array;
      Domain   : EW_Domain;
      Ada_Node : Node_Id)
      return W_Expr_Id
   with
     Pre => Is_Subprogram (Subp) and then Is_Hardcoded_Entity (Subp);
   --  Transform a hardcoded function call

   function Transform_Hardcoded_Procedure_Call
     (Subp     : Entity_Id;
      Args     : W_Expr_Array;
      Ada_Node : Node_Id)
      return W_Prog_Id
   with
     Pre => Is_Subprogram (Subp) and then Is_Hardcoded_Entity (Subp);
   --  Transform a hardcoded procedure call

   function Transform_Hardcoded_Literal
     (Call   : Node_Id;
      Domain : EW_Domain) return W_Expr_Id
   with
     Pre => Nkind (Call) = N_Function_Call
       and then Is_Hardcoded_Entity (Get_Called_Entity_For_Proof (Call))
       and then Is_Literal_Function (Get_Called_Entity_For_Proof (Call));
   --  Transform a literal of an hardcoded type in a precise way
   --  whenever possible. If no precise translation was achieved, return
   --  Why_Empty;

   function Transform_Hardcoded_Operation
     (Op                  : N_Binary_Op;
      Lty, Rty, Expr_Type : Type_Kind_Id;
      LT, RT              : W_Expr_Id;
      Domain              : EW_Domain;
      Ada_Node            : Node_Id)
      return W_Expr_Id
     with Pre => Is_Hardcoded_Operation (Op, Lty, Rty);
   --  Transform an operation "LT op RT" if "op" is hardcoded.

end Why.Gen.Hardcoded;
