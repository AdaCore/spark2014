------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - S P R I N T                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Text_IO;       use Ada.Text_IO;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;

with Namet;  use Namet;
with Uintp;  use Uintp;
with Urealp; use Urealp;

with Why.Atree.Accessors; use Why.Atree.Accessors;

package body Why.Atree.Sprint is

   O : Output_Id := Stdout;

   function Img (Value : Uint) return String;
   --  Helper function that return the Why image of a Uint

   ---------------------
   -- Sprint_Why_Node --
   ---------------------

   procedure Sprint_Why_Node (Node : Why_Node_Id; To : Output_Id := Stdout) is
      PS : Printer_State;
   begin
      O := To;
      Traverse (PS, Node);
   end Sprint_Why_Node;

   ---------
   -- Img --
   ---------

   function Img (Value : Uint) return String is
      Result : String := Int'Image (UI_To_Int (Value));
   begin
      return Trim (Result, Ada.Strings.Both);
   end Img;

   -----------------------
   -- Identifier_Pre_Op --
   -----------------------

   procedure Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Identifier_Id)
   is
      pragma Unreferenced (State);
   begin
      P (O, Get_Name_String (Get_Node (Node).Symbol));
   end Identifier_Pre_Op;

   ----------------------
   -- Type_Prop_Pre_Op --
   ----------------------

   procedure Type_Prop_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Prop_Id)
   is
   begin
      P (O, "prop");
   end Type_Prop_Pre_Op;

   ---------------------
   -- Type_Int_Pre_Op --
   ---------------------

   procedure Type_Int_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Int_Id)
   is
   begin
      P (O, "int");
   end Type_Int_Pre_Op;

   ----------------------
   -- Type_Bool_Pre_Op --
   ----------------------

   procedure Type_Bool_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Bool_Id)
   is
   begin
      P (O, "bool");
   end Type_Bool_Pre_Op;

   ----------------------
   -- Type_Real_Pre_Op --
   ----------------------

   procedure Type_Real_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Real_Id)
   is
   begin
      P (O, "real");
   end Type_Real_Pre_Op;

   ----------------------
   -- Type_Unit_Pre_Op --
   ----------------------

   procedure Type_Unit_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Unit_Id)
   is
   begin
      P (O, "unit");
   end Type_Unit_Pre_Op;

   --------------------------------
   -- Generic_Formal_Type_Pre_Op --
   --------------------------------

   procedure Generic_Formal_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Generic_Formal_Type_Id)
   is
   begin
      P (O, "'");
   end Generic_Formal_Type_Pre_Op;

   --------------------------------------
   -- Generic_Actual_Type_Chain_Pre_Op --
   --------------------------------------

   procedure Generic_Actual_Type_Chain_Pre_Op
     (State : in out Printer_State;
      Node  : W_Generic_Actual_Type_Chain_Id)
   is
      use Node_Lists;

      Types    : constant List :=
                   Get_List (Generic_Actual_Type_Chain_Get_Type_Chain (Node));
      Position : Cursor := First (Types);
   begin
      while Position /= No_Element loop
         declare
            Node : constant W_Primitive_Type_Id := Element (Position);
         begin
            Traverse (State, Node);
            P (O, " ");
         end;
      end loop;

      Traverse
        (State,
         Generic_Actual_Type_Chain_Get_Name (Node));

      State.Control := Abandon_Children;
   end Generic_Actual_Type_Chain_Pre_Op;

   ------------------------
   -- Array_Type_Post_Op --
   ------------------------

   procedure Array_Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Array_Type_Id)
   is
   begin
      P (O, " array");
   end Array_Type_Post_Op;

   ----------------------
   -- Ref_Type_Post_Op --
   ----------------------

   procedure Ref_Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Ref_Type_Id)
   is
   begin
      P (O, " ref");
   end Ref_Type_Post_Op;

   ---------------------------------
   -- Protected_Value_Type_Pre_Op --
   ---------------------------------

   procedure Protected_Value_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Protected_Value_Type_Id)
   is
   begin
      P (O, "(");
   end Protected_Value_Type_Pre_Op;

   ----------------------------------
   -- Protected_Value_Type_Post_Op --
   ----------------------------------

   procedure Protected_Value_Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Protected_Value_Type_Id)
   is
   begin
      P (O, ")");
   end Protected_Value_Type_Post_Op;

   ---------------------------------
   -- Anonymous_Arrow_Type_Pre_Op --
   ---------------------------------

   procedure Anonymous_Arrow_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Anonymous_Arrow_Type_Id)
   is
   begin
      Traverse
        (State,
         Anonymous_Arrow_Type_Get_Left (Node));

      P (O, " -> ");

      Traverse
        (State,
         Anonymous_Arrow_Type_Get_Right (Node));

      State.Control := Abandon_Children;
   end Anonymous_Arrow_Type_Pre_Op;

   -----------------------------
   -- Named_Arrow_Type_Pre_Op --
   -----------------------------

   procedure Named_Arrow_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Named_Arrow_Type_Id)
   is
   begin
      Traverse
        (State,
         Named_Arrow_Type_Get_Name (Node));
      P (O, " : ");
      Traverse
        (State,
         Named_Arrow_Type_Get_Left (Node));
      P (O, " -> ");
      Traverse
        (State,
         Named_Arrow_Type_Get_Right (Node));
      State.Control := Abandon_Children;
   end Named_Arrow_Type_Pre_Op;

   -----------------------------
   -- Computation_Spec_Pre_Op --
   -----------------------------

   procedure Computation_Spec_Pre_Op
     (State : in out Printer_State;
      Node  : W_Computation_Spec_Id)
   is
      Result : constant W_Identifier_OId :=
                 Computation_Spec_Get_Result_Name (Node);
   begin
      P (O, "{");
      Traverse (State,
                Computation_Spec_Get_Precondition (Node));
      PL (O, "}");

      if  Result /= Why_Empty then
         P (O, "returns ");
         Traverse
           (State,
            Computation_Spec_Get_Result_Name (Node));
         P (O, " : ");
      end if;

      Traverse
        (State,
         Computation_Spec_Get_Return_Type (Node));
      NL (O);

      Traverse
        (State,
         Computation_Spec_Get_Effects (Node));
      NL (O);

      P (O, "{");
      Traverse
        (State,
         Computation_Spec_Get_Postcondition (Node));
      P (O, "}");

      State.Control := Abandon_Children;
   end Computation_Spec_Pre_Op;

   -----------------------------
   -- Integer_Constant_Pre_Op --
   -----------------------------

   procedure Integer_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Integer_Constant_Id)
   is
   begin
      --  ??? The Why Reference does not give any detail about
      --  the syntax of integer constants. We shall suppose that
      --  it is similar to Ocaml's integer litterals:
      --
      --  IntegerLiteral ::=
      --     [-]  UnprefixedIntegerLiteral
      --
      --  UnprefixedIntegerLiteral ::=
      --      DecimalLiteral
      --      HexadecimalLiteral
      --      OctalLiteral
      --      BinaryLiteral
      --
      --  DecimalLiteral ::=
      --      DecimalLiteral  Digit
      --      DecimalLiteral  _
      --      Digit
      --
      --  HexadecimalLiteral ::=
      --      HexadecimalLiteral  HexadecimalDigit
      --      HexadecimalLiteral  _
      --      0x  HexadecimalDigit
      --      0X  HexadecimalDigit
      --
      --  OctalLiteral ::=
      --      OctalLiteral  OctalDigit
      --      OctalLiteral  _
      --      0o  OctalDigit
      --      0O  OctalDigit
      --
      --  BinaryLiteral ::=
      --      BinaryLiteral  BinaryDigit
      --      BinaryLiteral  _
      --      0b  BinaryDigit
      --      0B  BinaryDigit
      --
      --  Digit ::=
      --      DecimalDigit
      --
      --  HexadecimalDigit ::=  { 0123456789abcdefABCDEF }
      --
      --  DecimalDigit ::=  { 0123456789 }
      --
      --  OctalDigit ::=  { 01234567 }
      --
      --  BinaryDigit ::=  { 01 }

      P (O, Img (Integer_Constant_Get_Value (Node)));
   end Integer_Constant_Pre_Op;

   --------------------------
   -- Real_Constant_Pre_Op --
   --------------------------

   procedure Real_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Real_Constant_Id)
   is
      UR   : constant Ureal := Real_Constant_Get_Value (Node);
      Num  : constant Uint := Numerator (UR);
      Den  : constant Uint := Denominator (UR);
      Base : constant Nat := Rbase (UR);
   begin
      --  ??? Same remark as in the case of integer constants:
      --  I suppose that Why's real constants follows the same syntax
      --  as Ocaml's floating-point literals:
      --
      --      FloatingPointLiteral ::=
      --        [-]  UnprefixedFloatingPointLiteral
      --
      --      UnprefixedFloatingPointLiteral ::=
      --        DecimalLiteral  FractionalPart  ExponentPart
      --        DecimalLiteral  FractionalPart
      --        DecimalLiteral  ExponentPart
      --
      --      FractionalPart ::=
      --        FractionalPart  Digit
      --        FractionalPart  _
      --        .
      --
      --      ExponentPart ::=
      --        ExponentLetter  +  DecimalLiteral
      --        ExponentLetter  -  DecimalLiteral
      --        ExponentLetter     DecimalLiteral
      --
      --       ExponentLetter ::=  { eE }

      if UR_Is_Negative (UR) then
         P (O, "-");
      end if;

      if Base = 0 then
         P (O, Img (Num));
         P (O, "/");
         P (O, Img (Den));

      elsif Base = 10 then
         P (O, Img (Num));
         P (O, "E-");
         P (O, Img (Den));

      else
         P (O, Img (Num));

         if UI_To_Int (Den) > 0 then
            P (O, "/");
            P (O, Img ((UI_Expon (Den, Base))));

         elsif UI_To_Int (Den) < 0 then
            P (O, "*");
            P (O, Img ((UI_Expon (UI_Negate (Den), Base))));
         end if;
      end if;
   end Real_Constant_Pre_Op;

   -------------------------
   -- True_Literal_Pre_Op --
   -------------------------

   procedure True_Literal_Pre_Op
     (State : in out Printer_State;
      Node  : W_True_Literal_Id)
   is
   begin
      P (O, "true");
   end True_Literal_Pre_Op;

   --------------------------
   -- False_Literal_Pre_Op --
   --------------------------

   procedure False_Literal_Pre_Op
     (State : in out Printer_State;
      Node  : W_False_Literal_Id)
   is
   begin
      P (O, "false");
   end False_Literal_Pre_Op;

   -------------------------
   -- Void_Literal_Pre_Op --
   -------------------------

   procedure Void_Literal_Pre_Op
     (State : in out Printer_State;
      Node  : W_Void_Literal_Id)
   is
   begin
      P (O, "void");
   end Void_Literal_Pre_Op;

   ----------------------------
   -- Arith_Operation_Pre_Op --
   ----------------------------

   procedure Arith_Operation_Pre_Op
     (State : in out Printer_State;
      Node  : W_Arith_Operation_Id)
   is
   begin
      Traverse
        (State,
         Arith_Operation_Get_Left (Node));
      P (O, " ");
      Traverse
        (State,
         Arith_Operation_Get_Op (Node));
      P (O, " ");
      Traverse
        (State,
         Arith_Operation_Get_Right (Node));

      State.Control := Abandon_Children;
   end Arith_Operation_Pre_Op;

   --------------------------
   -- Negative_Term_Pre_Op --
   --------------------------

   procedure Negative_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Negative_Term_Id)
   is
   begin
      P (O, "-");
   end Negative_Term_Pre_Op;

   -----------------------------
   -- Label_Identifier_Pre_Op --
   -----------------------------

   procedure Label_Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Label_Identifier_Id)
   is
      Label : W_Identifier_OId := Label_Identifier_Get_Label (Node);
   begin
      Traverse
        (State,
         Label_Identifier_Get_Name (Node));

      if Label /= Why_Empty then
         P (O, "@");
         Traverse (State, Label);
      end if;

      State.Control := Abandon_Children;
   end Label_Identifier_Pre_Op;

   ----------------------
   -- Operation_Pre_Op --
   ----------------------

   procedure Operation_Pre_Op
     (State : in out Printer_State;
      Node  : W_Operation_Id)
   is
   begin
      Traverse
        (State,
         Operation_Get_Name (Node));
      P (O, " (");
      Traverse_List
        (State,
         Operation_Get_Parameters (Node));
      P (O, ")");
      State.Control := Abandon_Children;
   end Operation_Pre_Op;

   -----------------------
   -- Named_Term_Pre_Op --
   -----------------------

   procedure Named_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Named_Term_Id)
   is
   begin
      Traverse
        (State,
         Named_Term_Get_Name (Node));
      P (O, " [");
      Traverse
        (State,
         Named_Term_Get_Term (Node));
      P (O, "]");
      State.Control := Abandon_Children;
   end Named_Term_Pre_Op;

   -----------------------------
   -- Conditional_Term_Pre_Op --
   -----------------------------

   procedure Conditional_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Term_Id)
   is
      Condition : constant W_Term_Id :=
                    Conditional_Term_Get_Condition (Node);
      Then_Part : constant W_Term_Id :=
                    Conditional_Term_Get_Then_Part (Node);
      Else_Part : constant W_Term_Id :=
                    Conditional_Term_Get_Else_Part (Node);
      Has_Elsif : constant Boolean :=
                    Get_Kind (Else_Part) /= W_Conditional_Term;
   begin
      P (O, "if ");
      Traverse (State, Condition);
      PL (O, " then");
      Relative_Indent (O, 1);
      Traverse (State, Then_Part);
      NL (O);
      Relative_Indent (O, -1);
      P (O, " else");

      if not Has_Elsif then
         NL (O);
         Relative_Indent (O, 1);
      end if;

      Traverse (State, Else_Part);

      if not Has_Elsif then
         Relative_Indent (O, -1);
      end if;

      State.Control := Abandon_Children;
   end Conditional_Term_Pre_Op;

   -------------------------
   -- Binding_Term_Pre_Op --
   -------------------------

   procedure Binding_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Term_Id)
   is
      Name             : constant W_Identifier_Id :=
                           Binding_Term_Get_Name (Node);
      Def              : constant W_Term_Id :=
                           Binding_Term_Get_Def (Node);
      Context          : constant W_Term_Id :=
                           Binding_Term_Get_Context (Node);
      Binding_Sequence : constant Boolean :=
                           Get_Kind (Context) = W_Binding_Term;
   begin
      P (O, "let ");
      Traverse (State, Name);
      P (O, " = ");
      Traverse (State, Def);
      PL (O, " in");

      if not Binding_Sequence then
         Relative_Indent (O, 1);
      end if;

      Traverse (State, Context);

      if not Binding_Sequence then
         Relative_Indent (O, -1);
      end if;

      State.Control := Abandon_Children;
   end Binding_Term_Pre_Op;

   ---------------------------
   -- Protected_Term_Pre_Op --
   ---------------------------

   procedure Protected_Term_Pre_Op
     (State : in out Printer_State;
      Node  : W_Protected_Term_Id)
   is
   begin
      P (O, "(");
   end Protected_Term_Pre_Op;

   ----------------------------
   -- Protected_Term_Post_Op --
   ----------------------------

   procedure Protected_Term_Post_Op
     (State : in out Printer_State;
      Node  : W_Protected_Term_Id)
   is
   begin
      P (O, ")");
   end Protected_Term_Post_Op;

   -------------------
   -- Op_Add_Pre_Op --
   -------------------

   procedure Op_Add_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Add_Id)
   is
   begin
      P (O, "+");
   end Op_Add_Pre_Op;

   -------------------------
   -- Op_Substract_Pre_Op --
   -------------------------

   procedure Op_Substract_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Substract_Id)
   is
   begin
      P (O, "-");
   end Op_Substract_Pre_Op;

   ------------------------
   -- Op_Multiply_Pre_Op --
   ------------------------

   procedure Op_Multiply_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Multiply_Id)
   is
   begin
      P (O, "*");
   end Op_Multiply_Pre_Op;

   ----------------------
   -- Op_Divide_Pre_Op --
   ----------------------

   procedure Op_Divide_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Divide_Id)
   is
   begin
      P (O, "/");
   end Op_Divide_Pre_Op;

   ----------------------
   -- Op_Modulo_Pre_Op --
   ----------------------

   procedure Op_Modulo_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Modulo_Id)
   is
   begin
      P (O, "%");
   end Op_Modulo_Pre_Op;

   ------------------------------
   -- True_Literal_Pred_Pre_Op --
   ------------------------------

   procedure True_Literal_Pred_Pre_Op
     (State : in out Printer_State;
      Node  : W_True_Literal_Pred_Id)
   is
   begin
      raise Not_Implemented;
   end True_Literal_Pred_Pre_Op;

   -------------------------------
   -- True_Literal_Pred_Post_Op --
   -------------------------------

   procedure True_Literal_Pred_Post_Op
     (State : in out Printer_State;
      Node  : W_True_Literal_Pred_Id)
   is
   begin
      raise Not_Implemented;
   end True_Literal_Pred_Post_Op;

   -------------------------------
   -- False_Literal_Pred_Pre_Op --
   -------------------------------

   procedure False_Literal_Pred_Pre_Op
     (State : in out Printer_State;
      Node  : W_False_Literal_Pred_Id)
   is
   begin
      raise Not_Implemented;
   end False_Literal_Pred_Pre_Op;

   --------------------------------
   -- False_Literal_Pred_Post_Op --
   --------------------------------

   procedure False_Literal_Pred_Post_Op
     (State : in out Printer_State;
      Node  : W_False_Literal_Pred_Id)
   is
   begin
      raise Not_Implemented;
   end False_Literal_Pred_Post_Op;

   ---------------------------------
   -- Predicate_Identifier_Pre_Op --
   ---------------------------------

   procedure Predicate_Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Predicate_Identifier_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Predicate_Identifier_Get_Name (Node));
   end Predicate_Identifier_Pre_Op;

   ----------------------------------
   -- Predicate_Identifier_Post_Op --
   ----------------------------------

   procedure Predicate_Identifier_Post_Op
     (State : in out Printer_State;
      Node  : W_Predicate_Identifier_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Predicate_Identifier_Get_Name (Node));
   end Predicate_Identifier_Post_Op;

   -------------------------------
   -- Predicate_Instance_Pre_Op --
   -------------------------------

   procedure Predicate_Instance_Pre_Op
     (State : in out Printer_State;
      Node  : W_Predicate_Instance_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Predicate_Instance_Get_Name (Node));
      --  Traverse_List
      --    (State,
      --     Predicate_Instance_Get_Parameters (Node));
   end Predicate_Instance_Pre_Op;

   --------------------------------
   -- Predicate_Instance_Post_Op --
   --------------------------------

   procedure Predicate_Instance_Post_Op
     (State : in out Printer_State;
      Node  : W_Predicate_Instance_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Predicate_Instance_Get_Name (Node));
      --  Traverse_List
      --    (State,
      --     Predicate_Instance_Get_Parameters (Node));
   end Predicate_Instance_Post_Op;

   --------------------------
   -- Related_Terms_Pre_Op --
   --------------------------

   procedure Related_Terms_Pre_Op
     (State : in out Printer_State;
      Node  : W_Related_Terms_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Related_Terms_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Related_Terms_Get_Op (Node));
      --  Traverse
      --    (State,
      --     Related_Terms_Get_Right (Node));
      --  Traverse
      --    (State,
      --     Related_Terms_Get_Op2 (Node));
      --  Traverse
      --    (State,
      --     Related_Terms_Get_Right2 (Node));
   end Related_Terms_Pre_Op;

   ---------------------------
   -- Related_Terms_Post_Op --
   ---------------------------

   procedure Related_Terms_Post_Op
     (State : in out Printer_State;
      Node  : W_Related_Terms_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Related_Terms_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Related_Terms_Get_Op (Node));
      --  Traverse
      --    (State,
      --     Related_Terms_Get_Right (Node));
      --  Traverse
      --    (State,
      --     Related_Terms_Get_Op2 (Node));
      --  Traverse
      --    (State,
      --     Related_Terms_Get_Right2 (Node));
   end Related_Terms_Post_Op;

   ------------------------
   -- Implication_Pre_Op --
   ------------------------

   procedure Implication_Pre_Op
     (State : in out Printer_State;
      Node  : W_Implication_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Implication_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Implication_Get_Right (Node));
   end Implication_Pre_Op;

   -------------------------
   -- Implication_Post_Op --
   -------------------------

   procedure Implication_Post_Op
     (State : in out Printer_State;
      Node  : W_Implication_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Implication_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Implication_Get_Right (Node));
   end Implication_Post_Op;

   ------------------------
   -- Equivalence_Pre_Op --
   ------------------------

   procedure Equivalence_Pre_Op
     (State : in out Printer_State;
      Node  : W_Equivalence_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Equivalence_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Equivalence_Get_Right (Node));
   end Equivalence_Pre_Op;

   -------------------------
   -- Equivalence_Post_Op --
   -------------------------

   procedure Equivalence_Post_Op
     (State : in out Printer_State;
      Node  : W_Equivalence_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Equivalence_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Equivalence_Get_Right (Node));
   end Equivalence_Post_Op;

   ------------------------
   -- Disjonction_Pre_Op --
   ------------------------

   procedure Disjonction_Pre_Op
     (State : in out Printer_State;
      Node  : W_Disjonction_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Disjonction_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Disjonction_Get_Right (Node));
   end Disjonction_Pre_Op;

   -------------------------
   -- Disjonction_Post_Op --
   -------------------------

   procedure Disjonction_Post_Op
     (State : in out Printer_State;
      Node  : W_Disjonction_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Disjonction_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Disjonction_Get_Right (Node));
   end Disjonction_Post_Op;

   ------------------------
   -- Conjonction_Pre_Op --
   ------------------------

   procedure Conjonction_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conjonction_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Conjonction_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Conjonction_Get_Right (Node));
   end Conjonction_Pre_Op;

   -------------------------
   -- Conjonction_Post_Op --
   -------------------------

   procedure Conjonction_Post_Op
     (State : in out Printer_State;
      Node  : W_Conjonction_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Conjonction_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Conjonction_Get_Right (Node));
   end Conjonction_Post_Op;

   ---------------------
   -- Negation_Pre_Op --
   ---------------------

   procedure Negation_Pre_Op
     (State : in out Printer_State;
      Node  : W_Negation_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Negation_Get_Operand (Node));
   end Negation_Pre_Op;

   ----------------------
   -- Negation_Post_Op --
   ----------------------

   procedure Negation_Post_Op
     (State : in out Printer_State;
      Node  : W_Negation_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Negation_Get_Operand (Node));
   end Negation_Post_Op;

   -----------------------------
   -- Conditional_Pred_Pre_Op --
   -----------------------------

   procedure Conditional_Pred_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Pred_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Conditional_Pred_Get_Condition (Node));
      --  Traverse
      --    (State,
      --     Conditional_Pred_Get_Then_Part (Node));
      --  Traverse
      --    (State,
      --     Conditional_Pred_Get_Else_Part (Node));
   end Conditional_Pred_Pre_Op;

   ------------------------------
   -- Conditional_Pred_Post_Op --
   ------------------------------

   procedure Conditional_Pred_Post_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Pred_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Conditional_Pred_Get_Condition (Node));
      --  Traverse
      --    (State,
      --     Conditional_Pred_Get_Then_Part (Node));
      --  Traverse
      --    (State,
      --     Conditional_Pred_Get_Else_Part (Node));
   end Conditional_Pred_Post_Op;

   -------------------------
   -- Binding_Pred_Pre_Op --
   -------------------------

   procedure Binding_Pred_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Pred_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Binding_Pred_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Binding_Pred_Get_Def (Node));
      --  Traverse
      --    (State,
      --     Binding_Pred_Get_Context (Node));
   end Binding_Pred_Pre_Op;

   --------------------------
   -- Binding_Pred_Post_Op --
   --------------------------

   procedure Binding_Pred_Post_Op
     (State : in out Printer_State;
      Node  : W_Binding_Pred_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Binding_Pred_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Binding_Pred_Get_Def (Node));
      --  Traverse
      --    (State,
      --     Binding_Pred_Get_Context (Node));
   end Binding_Pred_Post_Op;

   ------------------------------
   -- Universal_Quantif_Pre_Op --
   ------------------------------

   procedure Universal_Quantif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Universal_Quantif_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Universal_Quantif_Get_Variables (Node));
      --  Traverse
      --    (State,
      --     Universal_Quantif_Get_Var_Type (Node));
      --  Traverse_List
      --    (State,
      --     Universal_Quantif_Get_Triggers (Node));
      --  Traverse
      --    (State,
      --     Universal_Quantif_Get_Pred (Node));
   end Universal_Quantif_Pre_Op;

   -------------------------------
   -- Universal_Quantif_Post_Op --
   -------------------------------

   procedure Universal_Quantif_Post_Op
     (State : in out Printer_State;
      Node  : W_Universal_Quantif_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Universal_Quantif_Get_Variables (Node));
      --  Traverse
      --    (State,
      --     Universal_Quantif_Get_Var_Type (Node));
      --  Traverse_List
      --    (State,
      --     Universal_Quantif_Get_Triggers (Node));
      --  Traverse
      --    (State,
      --     Universal_Quantif_Get_Pred (Node));
   end Universal_Quantif_Post_Op;

   --------------------------------
   -- Existential_Quantif_Pre_Op --
   --------------------------------

   procedure Existential_Quantif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Existential_Quantif_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Existential_Quantif_Get_Variables (Node));
      --  Traverse
      --    (State,
      --     Existential_Quantif_Get_Var_Type (Node));
      --  Traverse
      --    (State,
      --     Existential_Quantif_Get_Pred (Node));
   end Existential_Quantif_Pre_Op;

   ---------------------------------
   -- Existential_Quantif_Post_Op --
   ---------------------------------

   procedure Existential_Quantif_Post_Op
     (State : in out Printer_State;
      Node  : W_Existential_Quantif_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Existential_Quantif_Get_Variables (Node));
      --  Traverse
      --    (State,
      --     Existential_Quantif_Get_Var_Type (Node));
      --  Traverse
      --    (State,
      --     Existential_Quantif_Get_Pred (Node));
   end Existential_Quantif_Post_Op;

   ----------------------------
   -- Named_Predicate_Pre_Op --
   ----------------------------

   procedure Named_Predicate_Pre_Op
     (State : in out Printer_State;
      Node  : W_Named_Predicate_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Named_Predicate_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Named_Predicate_Get_Pred (Node));
   end Named_Predicate_Pre_Op;

   -----------------------------
   -- Named_Predicate_Post_Op --
   -----------------------------

   procedure Named_Predicate_Post_Op
     (State : in out Printer_State;
      Node  : W_Named_Predicate_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Named_Predicate_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Named_Predicate_Get_Pred (Node));
   end Named_Predicate_Post_Op;

   --------------------------------
   -- Protected_Predicate_Pre_Op --
   --------------------------------

   procedure Protected_Predicate_Pre_Op
     (State : in out Printer_State;
      Node  : W_Protected_Predicate_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Protected_Predicate_Get_Pred (Node));
   end Protected_Predicate_Pre_Op;

   ---------------------------------
   -- Protected_Predicate_Post_Op --
   ---------------------------------

   procedure Protected_Predicate_Post_Op
     (State : in out Printer_State;
      Node  : W_Protected_Predicate_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Protected_Predicate_Get_Pred (Node));
   end Protected_Predicate_Post_Op;

   ---------------------
   -- Triggers_Pre_Op --
   ---------------------

   procedure Triggers_Pre_Op
     (State : in out Printer_State;
      Node  : W_Triggers_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Triggers_Get_Triggers (Node));
   end Triggers_Pre_Op;

   ----------------------
   -- Triggers_Post_Op --
   ----------------------

   procedure Triggers_Post_Op
     (State : in out Printer_State;
      Node  : W_Triggers_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Triggers_Get_Triggers (Node));
   end Triggers_Post_Op;

   --------------------
   -- Trigger_Pre_Op --
   --------------------

   procedure Trigger_Pre_Op
     (State : in out Printer_State;
      Node  : W_Trigger_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Trigger_Get_Terms (Node));
   end Trigger_Pre_Op;

   ---------------------
   -- Trigger_Post_Op --
   ---------------------

   procedure Trigger_Post_Op
     (State : in out Printer_State;
      Node  : W_Trigger_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Trigger_Get_Terms (Node));
   end Trigger_Post_Op;

   -------------------
   -- Rel_Eq_Pre_Op --
   -------------------

   procedure Rel_Eq_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Eq_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Eq_Pre_Op;

   --------------------
   -- Rel_Eq_Post_Op --
   --------------------

   procedure Rel_Eq_Post_Op
     (State : in out Printer_State;
      Node  : W_Rel_Eq_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Eq_Post_Op;

   -------------------
   -- Rel_Ne_Pre_Op --
   -------------------

   procedure Rel_Ne_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Ne_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Ne_Pre_Op;

   --------------------
   -- Rel_Ne_Post_Op --
   --------------------

   procedure Rel_Ne_Post_Op
     (State : in out Printer_State;
      Node  : W_Rel_Ne_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Ne_Post_Op;

   -------------------
   -- Rel_Lt_Pre_Op --
   -------------------

   procedure Rel_Lt_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Lt_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Lt_Pre_Op;

   --------------------
   -- Rel_Lt_Post_Op --
   --------------------

   procedure Rel_Lt_Post_Op
     (State : in out Printer_State;
      Node  : W_Rel_Lt_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Lt_Post_Op;

   -------------------
   -- Rel_Le_Pre_Op --
   -------------------

   procedure Rel_Le_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Le_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Le_Pre_Op;

   --------------------
   -- Rel_Le_Post_Op --
   --------------------

   procedure Rel_Le_Post_Op
     (State : in out Printer_State;
      Node  : W_Rel_Le_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Le_Post_Op;

   -------------------
   -- Rel_Gt_Pre_Op --
   -------------------

   procedure Rel_Gt_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Gt_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Gt_Pre_Op;

   --------------------
   -- Rel_Gt_Post_Op --
   --------------------

   procedure Rel_Gt_Post_Op
     (State : in out Printer_State;
      Node  : W_Rel_Gt_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Gt_Post_Op;

   -------------------
   -- Rel_Ge_Pre_Op --
   -------------------

   procedure Rel_Ge_Pre_Op
     (State : in out Printer_State;
      Node  : W_Rel_Ge_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Ge_Pre_Op;

   --------------------
   -- Rel_Ge_Post_Op --
   --------------------

   procedure Rel_Ge_Post_Op
     (State : in out Printer_State;
      Node  : W_Rel_Ge_Id)
   is
   begin
      raise Not_Implemented;
   end Rel_Ge_Post_Op;

   ------------------
   -- Type_Post_Op --
   ------------------

   procedure Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Type_Id)
   is
      pragma Unreferenced (State);
   begin
      NL (O);
      --  Traverse
      --    (State,
      --     Type_Get_External (Node));
      --  Traverse_List
      --    (State,
      --     Type_Get_Type_Parameters (Node));
      --  Traverse
      --    (State,
      --     Type_Get_Name (Node));
   end Type_Post_Op;

   -----------------
   -- Type_Pre_Op --
   -----------------

   procedure Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Id)
   is
      pragma Unreferenced (State);
   begin
      P (O, "type ");
      --  Traverse
      --    (State,
      --     Type_Get_External (Node));
      --  Traverse_List
      --    (State,
      --     Type_Get_Type_Parameters (Node));
      --  Traverse
      --    (State,
      --     Type_Get_Name (Node));
   end Type_Pre_Op;

   ------------------
   -- Logic_Pre_Op --
   ------------------

   procedure Logic_Pre_Op
     (State : in out Printer_State;
      Node  : W_Logic_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Logic_Get_External (Node));
      --  Traverse_List
      --    (State,
      --     Logic_Get_Names (Node));
      --  Traverse
      --    (State,
      --     Logic_Get_Logic_Type (Node));
   end Logic_Pre_Op;

   -------------------
   -- Logic_Post_Op --
   -------------------

   procedure Logic_Post_Op
     (State : in out Printer_State;
      Node  : W_Logic_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Logic_Get_External (Node));
      --  Traverse_List
      --    (State,
      --     Logic_Get_Names (Node));
      --  Traverse
      --    (State,
      --     Logic_Get_Logic_Type (Node));
   end Logic_Post_Op;

   ---------------------
   -- Function_Pre_Op --
   ---------------------

   procedure Function_Pre_Op
     (State : in out Printer_State;
      Node  : W_Function_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Function_Get_Name (Node));
      --  Traverse_List
      --    (State,
      --     Function_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Function_Get_Return_Type (Node));
      --  Traverse
      --    (State,
      --     Function_Get_Def (Node));
   end Function_Pre_Op;

   ----------------------
   -- Function_Post_Op --
   ----------------------

   procedure Function_Post_Op
     (State : in out Printer_State;
      Node  : W_Function_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Function_Get_Name (Node));
      --  Traverse_List
      --    (State,
      --     Function_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Function_Get_Return_Type (Node));
      --  Traverse
      --    (State,
      --     Function_Get_Def (Node));
   end Function_Post_Op;

   ---------------------------------
   -- Predicate_Definition_Pre_Op --
   ---------------------------------

   procedure Predicate_Definition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Predicate_Definition_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Predicate_Definition_Get_Name (Node));
      --  Traverse_List
      --    (State,
      --     Predicate_Definition_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Predicate_Definition_Get_Def (Node));
   end Predicate_Definition_Pre_Op;

   ----------------------------------
   -- Predicate_Definition_Post_Op --
   ----------------------------------

   procedure Predicate_Definition_Post_Op
     (State : in out Printer_State;
      Node  : W_Predicate_Definition_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Predicate_Definition_Get_Name (Node));
      --  Traverse_List
      --    (State,
      --     Predicate_Definition_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Predicate_Definition_Get_Def (Node));
   end Predicate_Definition_Post_Op;

   ----------------------
   -- Inductive_Pre_Op --
   ----------------------

   procedure Inductive_Pre_Op
     (State : in out Printer_State;
      Node  : W_Inductive_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Inductive_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Inductive_Get_Logic_Type (Node));
      --  Traverse_List
      --    (State,
      --     Inductive_Get_Def (Node));
   end Inductive_Pre_Op;

   -----------------------
   -- Inductive_Post_Op --
   -----------------------

   procedure Inductive_Post_Op
     (State : in out Printer_State;
      Node  : W_Inductive_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Inductive_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Inductive_Get_Logic_Type (Node));
      --  Traverse_List
      --    (State,
      --     Inductive_Get_Def (Node));
   end Inductive_Post_Op;

   ------------------
   -- Axiom_Pre_Op --
   ------------------

   procedure Axiom_Pre_Op
     (State : in out Printer_State;
      Node  : W_Axiom_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Axiom_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Axiom_Get_Def (Node));
   end Axiom_Pre_Op;

   -------------------
   -- Axiom_Post_Op --
   -------------------

   procedure Axiom_Post_Op
     (State : in out Printer_State;
      Node  : W_Axiom_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Axiom_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Axiom_Get_Def (Node));
   end Axiom_Post_Op;

   -----------------
   -- Goal_Pre_Op --
   -----------------

   procedure Goal_Pre_Op
     (State : in out Printer_State;
      Node  : W_Goal_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Goal_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Goal_Get_Def (Node));
   end Goal_Pre_Op;

   ------------------
   -- Goal_Post_Op --
   ------------------

   procedure Goal_Post_Op
     (State : in out Printer_State;
      Node  : W_Goal_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Goal_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Goal_Get_Def (Node));
   end Goal_Post_Op;

   ---------------------
   -- External_Pre_Op --
   ---------------------

   procedure External_Pre_Op
     (State : in out Printer_State;
      Node  : W_External_Id)
   is
   begin
      raise Not_Implemented;
   end External_Pre_Op;

   ----------------------
   -- External_Post_Op --
   ----------------------

   procedure External_Post_Op
     (State : in out Printer_State;
      Node  : W_External_Id)
   is
   begin
      raise Not_Implemented;
   end External_Post_Op;

   -----------------------
   -- Logic_Type_Pre_Op --
   -----------------------

   procedure Logic_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Logic_Type_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Logic_Type_Get_Arg_Types (Node));
      --  Traverse_List
      --    (State,
      --     Logic_Type_Get_Return_Type (Node));
   end Logic_Type_Pre_Op;

   ------------------------
   -- Logic_Type_Post_Op --
   ------------------------

   procedure Logic_Type_Post_Op
     (State : in out Printer_State;
      Node  : W_Logic_Type_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Logic_Type_Get_Arg_Types (Node));
      --  Traverse_List
      --    (State,
      --     Logic_Type_Get_Return_Type (Node));
   end Logic_Type_Post_Op;

   -------------------------
   -- Logic_Binder_Pre_Op --
   -------------------------

   procedure Logic_Binder_Pre_Op
     (State : in out Printer_State;
      Node  : W_Logic_Binder_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Logic_Binder_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Logic_Binder_Get_Param_Type (Node));
   end Logic_Binder_Pre_Op;

   --------------------------
   -- Logic_Binder_Post_Op --
   --------------------------

   procedure Logic_Binder_Post_Op
     (State : in out Printer_State;
      Node  : W_Logic_Binder_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Logic_Binder_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Logic_Binder_Get_Param_Type (Node));
   end Logic_Binder_Post_Op;

   ---------------------------
   -- Inductive_Case_Pre_Op --
   ---------------------------

   procedure Inductive_Case_Pre_Op
     (State : in out Printer_State;
      Node  : W_Inductive_Case_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Inductive_Case_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Inductive_Case_Get_Pred (Node));
   end Inductive_Case_Pre_Op;

   ----------------------------
   -- Inductive_Case_Post_Op --
   ----------------------------

   procedure Inductive_Case_Post_Op
     (State : in out Printer_State;
      Node  : W_Inductive_Case_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Inductive_Case_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Inductive_Case_Get_Pred (Node));
   end Inductive_Case_Post_Op;

   --------------------
   -- Effects_Pre_Op --
   --------------------

   procedure Effects_Pre_Op
     (State : in out Printer_State;
      Node  : W_Effects_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Effects_Get_Reads (Node));
      --  Traverse_List
      --    (State,
      --     Effects_Get_Writes (Node));
      --  Traverse_List
      --    (State,
      --     Effects_Get_Raises (Node));
   end Effects_Pre_Op;

   ---------------------
   -- Effects_Post_Op --
   ---------------------

   procedure Effects_Post_Op
     (State : in out Printer_State;
      Node  : W_Effects_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Effects_Get_Reads (Node));
      --  Traverse_List
      --    (State,
      --     Effects_Get_Writes (Node));
      --  Traverse_List
      --    (State,
      --     Effects_Get_Raises (Node));
   end Effects_Post_Op;

   -------------------------
   -- Precondition_Pre_Op --
   -------------------------

   procedure Precondition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Precondition_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Precondition_Get_Assertion (Node));
   end Precondition_Pre_Op;

   --------------------------
   -- Precondition_Post_Op --
   --------------------------

   procedure Precondition_Post_Op
     (State : in out Printer_State;
      Node  : W_Precondition_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Precondition_Get_Assertion (Node));
   end Precondition_Post_Op;

   --------------------------
   -- Postcondition_Pre_Op --
   --------------------------

   procedure Postcondition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Postcondition_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Postcondition_Get_Assertion (Node));
      --  Traverse_List
      --    (State,
      --     Postcondition_Get_Handlers (Node));
   end Postcondition_Pre_Op;

   ---------------------------
   -- Postcondition_Post_Op --
   ---------------------------

   procedure Postcondition_Post_Op
     (State : in out Printer_State;
      Node  : W_Postcondition_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Postcondition_Get_Assertion (Node));
      --  Traverse_List
      --    (State,
      --     Postcondition_Get_Handlers (Node));
   end Postcondition_Post_Op;

   --------------------------
   -- Exn_Condition_Pre_Op --
   --------------------------

   procedure Exn_Condition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Exn_Condition_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Exn_Condition_Get_Exn_Case (Node));
      --  Traverse
      --    (State,
      --     Exn_Condition_Get_Assertion (Node));
   end Exn_Condition_Pre_Op;

   ---------------------------
   -- Exn_Condition_Post_Op --
   ---------------------------

   procedure Exn_Condition_Post_Op
     (State : in out Printer_State;
      Node  : W_Exn_Condition_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Exn_Condition_Get_Exn_Case (Node));
      --  Traverse
      --    (State,
      --     Exn_Condition_Get_Assertion (Node));
   end Exn_Condition_Post_Op;

   ----------------------
   -- Assertion_Pre_Op --
   ----------------------

   procedure Assertion_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assertion_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Assertion_Get_Pred (Node));
      --  Traverse
      --    (State,
      --     Assertion_Get_As (Node));
   end Assertion_Pre_Op;

   -----------------------
   -- Assertion_Post_Op --
   -----------------------

   procedure Assertion_Post_Op
     (State : in out Printer_State;
      Node  : W_Assertion_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Assertion_Get_Pred (Node));
      --  Traverse
      --    (State,
      --     Assertion_Get_As (Node));
   end Assertion_Post_Op;

   --------------------------
   -- Prog_Constant_Pre_Op --
   --------------------------

   procedure Prog_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Prog_Constant_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Prog_Constant_Get_Def (Node));
   end Prog_Constant_Pre_Op;

   ---------------------------
   -- Prog_Constant_Post_Op --
   ---------------------------

   procedure Prog_Constant_Post_Op
     (State : in out Printer_State;
      Node  : W_Prog_Constant_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Prog_Constant_Get_Def (Node));
   end Prog_Constant_Post_Op;

   ----------------------------
   -- Prog_Identifier_Pre_Op --
   ----------------------------

   procedure Prog_Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Prog_Identifier_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Prog_Identifier_Get_Def (Node));
   end Prog_Identifier_Pre_Op;

   -----------------------------
   -- Prog_Identifier_Post_Op --
   -----------------------------

   procedure Prog_Identifier_Post_Op
     (State : in out Printer_State;
      Node  : W_Prog_Identifier_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Prog_Identifier_Get_Def (Node));
   end Prog_Identifier_Post_Op;

   ------------------
   -- Deref_Pre_Op --
   ------------------

   procedure Deref_Pre_Op
     (State : in out Printer_State;
      Node  : W_Deref_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Deref_Get_Ref (Node));
   end Deref_Pre_Op;

   -------------------
   -- Deref_Post_Op --
   -------------------

   procedure Deref_Post_Op
     (State : in out Printer_State;
      Node  : W_Deref_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Deref_Get_Ref (Node));
   end Deref_Post_Op;

   -----------------------
   -- Assignment_Pre_Op --
   -----------------------

   procedure Assignment_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assignment_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Assignment_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Assignment_Get_Value (Node));
   end Assignment_Pre_Op;

   ------------------------
   -- Assignment_Post_Op --
   ------------------------

   procedure Assignment_Post_Op
     (State : in out Printer_State;
      Node  : W_Assignment_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Assignment_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Assignment_Get_Value (Node));
   end Assignment_Post_Op;

   -------------------------
   -- Array_Access_Pre_Op --
   -------------------------

   procedure Array_Access_Pre_Op
     (State : in out Printer_State;
      Node  : W_Array_Access_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Array_Access_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Array_Access_Get_Index (Node));
   end Array_Access_Pre_Op;

   --------------------------
   -- Array_Access_Post_Op --
   --------------------------

   procedure Array_Access_Post_Op
     (State : in out Printer_State;
      Node  : W_Array_Access_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Array_Access_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Array_Access_Get_Index (Node));
   end Array_Access_Post_Op;

   -------------------------
   -- Array_Update_Pre_Op --
   -------------------------

   procedure Array_Update_Pre_Op
     (State : in out Printer_State;
      Node  : W_Array_Update_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Array_Update_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Array_Update_Get_Index (Node));
      --  Traverse
      --    (State,
      --     Array_Update_Get_Value (Node));
   end Array_Update_Pre_Op;

   --------------------------
   -- Array_Update_Post_Op --
   --------------------------

   procedure Array_Update_Post_Op
     (State : in out Printer_State;
      Node  : W_Array_Update_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Array_Update_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Array_Update_Get_Index (Node));
      --  Traverse
      --    (State,
      --     Array_Update_Get_Value (Node));
   end Array_Update_Post_Op;

   -----------------------
   -- Infix_Call_Pre_Op --
   -----------------------

   procedure Infix_Call_Pre_Op
     (State : in out Printer_State;
      Node  : W_Infix_Call_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Infix_Call_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Infix_Call_Get_Infix (Node));
      --  Traverse
      --    (State,
      --     Infix_Call_Get_Right (Node));
   end Infix_Call_Pre_Op;

   ------------------------
   -- Infix_Call_Post_Op --
   ------------------------

   procedure Infix_Call_Post_Op
     (State : in out Printer_State;
      Node  : W_Infix_Call_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Infix_Call_Get_Left (Node));
      --  Traverse
      --    (State,
      --     Infix_Call_Get_Infix (Node));
      --  Traverse
      --    (State,
      --     Infix_Call_Get_Right (Node));
   end Infix_Call_Post_Op;

   ------------------------
   -- Prefix_Call_Pre_Op --
   ------------------------

   procedure Prefix_Call_Pre_Op
     (State : in out Printer_State;
      Node  : W_Prefix_Call_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Prefix_Call_Get_Prefix (Node));
      --  Traverse
      --    (State,
      --     Prefix_Call_Get_Operand (Node));
   end Prefix_Call_Pre_Op;

   -------------------------
   -- Prefix_Call_Post_Op --
   -------------------------

   procedure Prefix_Call_Post_Op
     (State : in out Printer_State;
      Node  : W_Prefix_Call_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Prefix_Call_Get_Prefix (Node));
      --  Traverse
      --    (State,
      --     Prefix_Call_Get_Operand (Node));
   end Prefix_Call_Post_Op;

   -------------------------
   -- Binding_Prog_Pre_Op --
   -------------------------

   procedure Binding_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Prog_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Binding_Prog_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Binding_Prog_Get_Def (Node));
      --  Traverse
      --    (State,
      --     Binding_Prog_Get_Context (Node));
   end Binding_Prog_Pre_Op;

   --------------------------
   -- Binding_Prog_Post_Op --
   --------------------------

   procedure Binding_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Binding_Prog_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Binding_Prog_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Binding_Prog_Get_Def (Node));
      --  Traverse
      --    (State,
      --     Binding_Prog_Get_Context (Node));
   end Binding_Prog_Post_Op;

   ------------------------
   -- Binding_Ref_Pre_Op --
   ------------------------

   procedure Binding_Ref_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Ref_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Binding_Ref_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Binding_Ref_Get_Def (Node));
      --  Traverse
      --    (State,
      --     Binding_Ref_Get_Context (Node));
   end Binding_Ref_Pre_Op;

   -------------------------
   -- Binding_Ref_Post_Op --
   -------------------------

   procedure Binding_Ref_Post_Op
     (State : in out Printer_State;
      Node  : W_Binding_Ref_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Binding_Ref_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Binding_Ref_Get_Def (Node));
      --  Traverse
      --    (State,
      --     Binding_Ref_Get_Context (Node));
   end Binding_Ref_Post_Op;

   -----------------------------
   -- Conditional_Prog_Pre_Op --
   -----------------------------

   procedure Conditional_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Prog_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Conditional_Prog_Get_Condition (Node));
      --  Traverse
      --    (State,
      --     Conditional_Prog_Get_Then_Part (Node));
      --  Traverse
      --    (State,
      --     Conditional_Prog_Get_Else_Part (Node));
   end Conditional_Prog_Pre_Op;

   ------------------------------
   -- Conditional_Prog_Post_Op --
   ------------------------------

   procedure Conditional_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Prog_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Conditional_Prog_Get_Condition (Node));
      --  Traverse
      --    (State,
      --     Conditional_Prog_Get_Then_Part (Node));
      --  Traverse
      --    (State,
      --     Conditional_Prog_Get_Else_Part (Node));
   end Conditional_Prog_Post_Op;

   -----------------------
   -- While_Loop_Pre_Op --
   -----------------------

   procedure While_Loop_Pre_Op
     (State : in out Printer_State;
      Node  : W_While_Loop_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     While_Loop_Get_Condition (Node));
      --  Traverse
      --    (State,
      --     While_Loop_Get_Annotation (Node));
      --  Traverse
      --    (State,
      --     While_Loop_Get_Loop_Content (Node));
   end While_Loop_Pre_Op;

   ------------------------
   -- While_Loop_Post_Op --
   ------------------------

   procedure While_Loop_Post_Op
     (State : in out Printer_State;
      Node  : W_While_Loop_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     While_Loop_Get_Condition (Node));
      --  Traverse
      --    (State,
      --     While_Loop_Get_Annotation (Node));
      --  Traverse
      --    (State,
      --     While_Loop_Get_Loop_Content (Node));
   end While_Loop_Post_Op;

   -------------------------------
   -- Statement_Sequence_Pre_Op --
   -------------------------------

   procedure Statement_Sequence_Pre_Op
     (State : in out Printer_State;
      Node  : W_Statement_Sequence_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Statement_Sequence_Get_Statements (Node));
   end Statement_Sequence_Pre_Op;

   --------------------------------
   -- Statement_Sequence_Post_Op --
   --------------------------------

   procedure Statement_Sequence_Post_Op
     (State : in out Printer_State;
      Node  : W_Statement_Sequence_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Statement_Sequence_Get_Statements (Node));
   end Statement_Sequence_Post_Op;

   ------------------
   -- Label_Pre_Op --
   ------------------

   procedure Label_Pre_Op
     (State : in out Printer_State;
      Node  : W_Label_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Label_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Label_Get_Def (Node));
   end Label_Pre_Op;

   -------------------
   -- Label_Post_Op --
   -------------------

   procedure Label_Post_Op
     (State : in out Printer_State;
      Node  : W_Label_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Label_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Label_Get_Def (Node));
   end Label_Post_Op;

   -------------------
   -- Assert_Pre_Op --
   -------------------

   procedure Assert_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assert_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Assert_Get_Assertions (Node));
      --  Traverse
      --    (State,
      --     Assert_Get_Prog (Node));
   end Assert_Pre_Op;

   --------------------
   -- Assert_Post_Op --
   --------------------

   procedure Assert_Post_Op
     (State : in out Printer_State;
      Node  : W_Assert_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Assert_Get_Assertions (Node));
      --  Traverse
      --    (State,
      --     Assert_Get_Prog (Node));
   end Assert_Post_Op;

   ---------------------------
   -- Post_Assertion_Pre_Op --
   ---------------------------

   procedure Post_Assertion_Pre_Op
     (State : in out Printer_State;
      Node  : W_Post_Assertion_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Post_Assertion_Get_Prog (Node));
      --  Traverse
      --    (State,
      --     Post_Assertion_Get_Post (Node));
   end Post_Assertion_Pre_Op;

   ----------------------------
   -- Post_Assertion_Post_Op --
   ----------------------------

   procedure Post_Assertion_Post_Op
     (State : in out Printer_State;
      Node  : W_Post_Assertion_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Post_Assertion_Get_Prog (Node));
      --  Traverse
      --    (State,
      --     Post_Assertion_Get_Post (Node));
   end Post_Assertion_Post_Op;

   -----------------------------
   -- Opaque_Assertion_Pre_Op --
   -----------------------------

   procedure Opaque_Assertion_Pre_Op
     (State : in out Printer_State;
      Node  : W_Opaque_Assertion_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Opaque_Assertion_Get_Prog (Node));
      --  Traverse
      --    (State,
      --     Opaque_Assertion_Get_Post (Node));
   end Opaque_Assertion_Pre_Op;

   ------------------------------
   -- Opaque_Assertion_Post_Op --
   ------------------------------

   procedure Opaque_Assertion_Post_Op
     (State : in out Printer_State;
      Node  : W_Opaque_Assertion_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Opaque_Assertion_Get_Prog (Node));
      --  Traverse
      --    (State,
      --     Opaque_Assertion_Get_Post (Node));
   end Opaque_Assertion_Post_Op;

   --------------------
   -- Fun_Def_Pre_Op --
   --------------------

   procedure Fun_Def_Pre_Op
     (State : in out Printer_State;
      Node  : W_Fun_Def_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Fun_Def_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Fun_Def_Get_Def (Node));
   end Fun_Def_Pre_Op;

   ---------------------
   -- Fun_Def_Post_Op --
   ---------------------

   procedure Fun_Def_Post_Op
     (State : in out Printer_State;
      Node  : W_Fun_Def_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Fun_Def_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Fun_Def_Get_Def (Node));
   end Fun_Def_Post_Op;

   ------------------------
   -- Binding_Fun_Pre_Op --
   ------------------------

   procedure Binding_Fun_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Fun_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Binding_Fun_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Binding_Fun_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Binding_Fun_Get_Def (Node));
      --  Traverse
      --    (State,
      --     Binding_Fun_Get_Context (Node));
   end Binding_Fun_Pre_Op;

   -------------------------
   -- Binding_Fun_Post_Op --
   -------------------------

   procedure Binding_Fun_Post_Op
     (State : in out Printer_State;
      Node  : W_Binding_Fun_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Binding_Fun_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Binding_Fun_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Binding_Fun_Get_Def (Node));
      --  Traverse
      --    (State,
      --     Binding_Fun_Get_Context (Node));
   end Binding_Fun_Post_Op;

   ------------------------
   -- Binding_Rec_Pre_Op --
   ------------------------

   procedure Binding_Rec_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Rec_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Binding_Rec_Get_Recfun (Node));
      --  Traverse
      --    (State,
      --     Binding_Rec_Get_Context (Node));
   end Binding_Rec_Pre_Op;

   -------------------------
   -- Binding_Rec_Post_Op --
   -------------------------

   procedure Binding_Rec_Post_Op
     (State : in out Printer_State;
      Node  : W_Binding_Rec_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Binding_Rec_Get_Recfun (Node));
      --  Traverse
      --    (State,
      --     Binding_Rec_Get_Context (Node));
   end Binding_Rec_Post_Op;

   --------------------------
   -- Prog_Sequence_Pre_Op --
   --------------------------

   procedure Prog_Sequence_Pre_Op
     (State : in out Printer_State;
      Node  : W_Prog_Sequence_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Prog_Sequence_Get_Progs (Node));
   end Prog_Sequence_Pre_Op;

   ---------------------------
   -- Prog_Sequence_Post_Op --
   ---------------------------

   procedure Prog_Sequence_Post_Op
     (State : in out Printer_State;
      Node  : W_Prog_Sequence_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Prog_Sequence_Get_Progs (Node));
   end Prog_Sequence_Post_Op;

   ----------------------------
   -- Raise_Statement_Pre_Op --
   ----------------------------

   procedure Raise_Statement_Pre_Op
     (State : in out Printer_State;
      Node  : W_Raise_Statement_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Raise_Statement_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Raise_Statement_Get_Exn_Type (Node));
   end Raise_Statement_Pre_Op;

   -----------------------------
   -- Raise_Statement_Post_Op --
   -----------------------------

   procedure Raise_Statement_Post_Op
     (State : in out Printer_State;
      Node  : W_Raise_Statement_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Raise_Statement_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Raise_Statement_Get_Exn_Type (Node));
   end Raise_Statement_Post_Op;

   --------------------------------------------
   -- Raise_Statement_With_Parameters_Pre_Op --
   --------------------------------------------

   procedure Raise_Statement_With_Parameters_Pre_Op
     (State : in out Printer_State;
      Node  : W_Raise_Statement_With_Parameters_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Raise_Statement_With_Parameters_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Raise_Statement_With_Parameters_Get_Parameter (Node));
      --  Traverse
      --    (State,
      --     Raise_Statement_With_Parameters_Get_Exn_Type (Node));
   end Raise_Statement_With_Parameters_Pre_Op;

   ---------------------------------------------
   -- Raise_Statement_With_Parameters_Post_Op --
   ---------------------------------------------

   procedure Raise_Statement_With_Parameters_Post_Op
     (State : in out Printer_State;
      Node  : W_Raise_Statement_With_Parameters_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Raise_Statement_With_Parameters_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Raise_Statement_With_Parameters_Get_Parameter (Node));
      --  Traverse
      --    (State,
      --     Raise_Statement_With_Parameters_Get_Exn_Type (Node));
   end Raise_Statement_With_Parameters_Post_Op;

   ----------------------
   -- Try_Block_Pre_Op --
   ----------------------

   procedure Try_Block_Pre_Op
     (State : in out Printer_State;
      Node  : W_Try_Block_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Try_Block_Get_Prog (Node));
      --  Traverse_List
      --    (State,
      --     Try_Block_Get_Handler (Node));
   end Try_Block_Pre_Op;

   -----------------------
   -- Try_Block_Post_Op --
   -----------------------

   procedure Try_Block_Post_Op
     (State : in out Printer_State;
      Node  : W_Try_Block_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Try_Block_Get_Prog (Node));
      --  Traverse_List
      --    (State,
      --     Try_Block_Get_Handler (Node));
   end Try_Block_Post_Op;

   -----------------------------
   -- Unreachable_Code_Pre_Op --
   -----------------------------

   procedure Unreachable_Code_Pre_Op
     (State : in out Printer_State;
      Node  : W_Unreachable_Code_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Unreachable_Code_Get_Exn_Type (Node));
   end Unreachable_Code_Pre_Op;

   ------------------------------
   -- Unreachable_Code_Post_Op --
   ------------------------------

   procedure Unreachable_Code_Post_Op
     (State : in out Printer_State;
      Node  : W_Unreachable_Code_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Unreachable_Code_Get_Exn_Type (Node));
   end Unreachable_Code_Post_Op;

   ------------------------
   -- Begin_Block_Pre_Op --
   ------------------------

   procedure Begin_Block_Pre_Op
     (State : in out Printer_State;
      Node  : W_Begin_Block_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Begin_Block_Get_Prog (Node));
   end Begin_Block_Pre_Op;

   -------------------------
   -- Begin_Block_Post_Op --
   -------------------------

   procedure Begin_Block_Post_Op
     (State : in out Printer_State;
      Node  : W_Begin_Block_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Begin_Block_Get_Prog (Node));
   end Begin_Block_Post_Op;

   ---------------------------
   -- Protected_Prog_Pre_Op --
   ---------------------------

   procedure Protected_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Protected_Prog_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Protected_Prog_Get_Prog (Node));
   end Protected_Prog_Pre_Op;

   ----------------------------
   -- Protected_Prog_Post_Op --
   ----------------------------

   procedure Protected_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Protected_Prog_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Protected_Prog_Get_Prog (Node));
   end Protected_Prog_Post_Op;

   ------------------------
   -- Op_Add_Prog_Pre_Op --
   ------------------------

   procedure Op_Add_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Add_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Add_Prog_Pre_Op;

   -------------------------
   -- Op_Add_Prog_Post_Op --
   -------------------------

   procedure Op_Add_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Add_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Add_Prog_Post_Op;

   ------------------------------
   -- Op_Substract_Prog_Pre_Op --
   ------------------------------

   procedure Op_Substract_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Substract_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Substract_Prog_Pre_Op;

   -------------------------------
   -- Op_Substract_Prog_Post_Op --
   -------------------------------

   procedure Op_Substract_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Substract_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Substract_Prog_Post_Op;

   -----------------------------
   -- Op_Multiply_Prog_Pre_Op --
   -----------------------------

   procedure Op_Multiply_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Multiply_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Multiply_Prog_Pre_Op;

   ------------------------------
   -- Op_Multiply_Prog_Post_Op --
   ------------------------------

   procedure Op_Multiply_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Multiply_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Multiply_Prog_Post_Op;

   ---------------------------
   -- Op_Divide_Prog_Pre_Op --
   ---------------------------

   procedure Op_Divide_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Divide_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Divide_Prog_Pre_Op;

   ----------------------------
   -- Op_Divide_Prog_Post_Op --
   ----------------------------

   procedure Op_Divide_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Divide_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Divide_Prog_Post_Op;

   ------------------------
   -- Op_Mod_Prog_Pre_Op --
   ------------------------

   procedure Op_Mod_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Mod_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Mod_Prog_Pre_Op;

   -------------------------
   -- Op_Mod_Prog_Post_Op --
   -------------------------

   procedure Op_Mod_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Mod_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Mod_Prog_Post_Op;

   -----------------------
   -- Op_Eq_Prog_Pre_Op --
   -----------------------

   procedure Op_Eq_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Eq_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Eq_Prog_Pre_Op;

   ------------------------
   -- Op_Eq_Prog_Post_Op --
   ------------------------

   procedure Op_Eq_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Eq_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Eq_Prog_Post_Op;

   -----------------------
   -- Op_Ne_Prog_Pre_Op --
   -----------------------

   procedure Op_Ne_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Ne_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Ne_Prog_Pre_Op;

   ------------------------
   -- Op_Ne_Prog_Post_Op --
   ------------------------

   procedure Op_Ne_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Ne_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Ne_Prog_Post_Op;

   -----------------------
   -- Op_Lt_Prog_Pre_Op --
   -----------------------

   procedure Op_Lt_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Lt_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Lt_Prog_Pre_Op;

   ------------------------
   -- Op_Lt_Prog_Post_Op --
   ------------------------

   procedure Op_Lt_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Lt_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Lt_Prog_Post_Op;

   -----------------------
   -- Op_Le_Prog_Pre_Op --
   -----------------------

   procedure Op_Le_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Le_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Le_Prog_Pre_Op;

   ------------------------
   -- Op_Le_Prog_Post_Op --
   ------------------------

   procedure Op_Le_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Le_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Le_Prog_Post_Op;

   -----------------------
   -- Op_Gt_Prog_Pre_Op --
   -----------------------

   procedure Op_Gt_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Gt_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Gt_Prog_Pre_Op;

   ------------------------
   -- Op_Gt_Prog_Post_Op --
   ------------------------

   procedure Op_Gt_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Gt_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Gt_Prog_Post_Op;

   -----------------------
   -- Op_Ge_Prog_Pre_Op --
   -----------------------

   procedure Op_Ge_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Ge_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Ge_Prog_Pre_Op;

   ------------------------
   -- Op_Ge_Prog_Post_Op --
   ------------------------

   procedure Op_Ge_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Ge_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Ge_Prog_Post_Op;

   ----------------------------
   -- Op_Or_Else_Prog_Pre_Op --
   ----------------------------

   procedure Op_Or_Else_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Or_Else_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Or_Else_Prog_Pre_Op;

   -----------------------------
   -- Op_Or_Else_Prog_Post_Op --
   -----------------------------

   procedure Op_Or_Else_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Or_Else_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Or_Else_Prog_Post_Op;

   -----------------------------
   -- Op_And_Then_Prog_Pre_Op --
   -----------------------------

   procedure Op_And_Then_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_And_Then_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_And_Then_Prog_Pre_Op;

   ------------------------------
   -- Op_And_Then_Prog_Post_Op --
   ------------------------------

   procedure Op_And_Then_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_And_Then_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_And_Then_Prog_Post_Op;

   --------------------------
   -- Op_Minus_Prog_Pre_Op --
   --------------------------

   procedure Op_Minus_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Minus_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Minus_Prog_Pre_Op;

   ---------------------------
   -- Op_Minus_Prog_Post_Op --
   ---------------------------

   procedure Op_Minus_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Minus_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Minus_Prog_Post_Op;

   ------------------------
   -- Op_Not_Prog_Pre_Op --
   ------------------------

   procedure Op_Not_Prog_Pre_Op
     (State : in out Printer_State;
      Node  : W_Op_Not_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Not_Prog_Pre_Op;

   -------------------------
   -- Op_Not_Prog_Post_Op --
   -------------------------

   procedure Op_Not_Prog_Post_Op
     (State : in out Printer_State;
      Node  : W_Op_Not_Prog_Id)
   is
   begin
      raise Not_Implemented;
   end Op_Not_Prog_Post_Op;

   --------------------
   -- Binders_Pre_Op --
   --------------------

   procedure Binders_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binders_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Binders_Get_Binders (Node));
   end Binders_Pre_Op;

   ---------------------
   -- Binders_Post_Op --
   ---------------------

   procedure Binders_Post_Op
     (State : in out Printer_State;
      Node  : W_Binders_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Binders_Get_Binders (Node));
   end Binders_Post_Op;

   -------------------
   -- Binder_Pre_Op --
   -------------------

   procedure Binder_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binder_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Binder_Get_Names (Node));
      --  Traverse
      --    (State,
      --     Binder_Get_Arg_Type (Node));
   end Binder_Pre_Op;

   --------------------
   -- Binder_Post_Op --
   --------------------

   procedure Binder_Post_Op
     (State : in out Printer_State;
      Node  : W_Binder_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     Binder_Get_Names (Node));
      --  Traverse
      --    (State,
      --     Binder_Get_Arg_Type (Node));
   end Binder_Post_Op;

   -------------------
   -- Recfun_Pre_Op --
   -------------------

   procedure Recfun_Pre_Op
     (State : in out Printer_State;
      Node  : W_Recfun_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Recfun_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Recfun_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Recfun_Get_Return_Type (Node));
      --  Traverse
      --    (State,
      --     Recfun_Get_Variant (Node));
      --  Traverse
      --    (State,
      --     Recfun_Get_Def (Node));
   end Recfun_Pre_Op;

   --------------------
   -- Recfun_Post_Op --
   --------------------

   procedure Recfun_Post_Op
     (State : in out Printer_State;
      Node  : W_Recfun_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Recfun_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Recfun_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Recfun_Get_Return_Type (Node));
      --  Traverse
      --    (State,
      --     Recfun_Get_Variant (Node));
      --  Traverse
      --    (State,
      --     Recfun_Get_Def (Node));
   end Recfun_Post_Op;

   -----------------------
   -- Loop_Annot_Pre_Op --
   -----------------------

   procedure Loop_Annot_Pre_Op
     (State : in out Printer_State;
      Node  : W_Loop_Annot_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Loop_Annot_Get_Invariant (Node));
      --  Traverse
      --    (State,
      --     Loop_Annot_Get_Variant (Node));
   end Loop_Annot_Pre_Op;

   ------------------------
   -- Loop_Annot_Post_Op --
   ------------------------

   procedure Loop_Annot_Post_Op
     (State : in out Printer_State;
      Node  : W_Loop_Annot_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Loop_Annot_Get_Invariant (Node));
      --  Traverse
      --    (State,
      --     Loop_Annot_Get_Variant (Node));
   end Loop_Annot_Post_Op;

   -------------------
   -- Wf_Arg_Pre_Op --
   -------------------

   procedure Wf_Arg_Pre_Op
     (State : in out Printer_State;
      Node  : W_Wf_Arg_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Wf_Arg_Get_Def (Node));
      --  Traverse
      --    (State,
      --     Wf_Arg_Get_For_Id (Node));
   end Wf_Arg_Pre_Op;

   --------------------
   -- Wf_Arg_Post_Op --
   --------------------

   procedure Wf_Arg_Post_Op
     (State : in out Printer_State;
      Node  : W_Wf_Arg_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Wf_Arg_Get_Def (Node));
      --  Traverse
      --    (State,
      --     Wf_Arg_Get_For_Id (Node));
   end Wf_Arg_Post_Op;

   --------------------
   -- Handler_Pre_Op --
   --------------------

   procedure Handler_Pre_Op
     (State : in out Printer_State;
      Node  : W_Handler_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Handler_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Handler_Get_Parameter (Node));
      --  Traverse
      --    (State,
      --     Handler_Get_Def (Node));
   end Handler_Pre_Op;

   ---------------------
   -- Handler_Post_Op --
   ---------------------

   procedure Handler_Post_Op
     (State : in out Printer_State;
      Node  : W_Handler_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Handler_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Handler_Get_Parameter (Node));
      --  Traverse
      --    (State,
      --     Handler_Get_Def (Node));
   end Handler_Post_Op;

   -----------------
   -- File_Pre_Op --
   -----------------

   procedure File_Pre_Op
     (State : in out Printer_State;
      Node  : W_File_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     File_Get_Declarations (Node));
   end File_Pre_Op;

   ------------------
   -- File_Post_Op --
   ------------------

   procedure File_Post_Op
     (State : in out Printer_State;
      Node  : W_File_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse_List
      --    (State,
      --     File_Get_Declarations (Node));
   end File_Post_Op;

   ---------------------------
   -- Global_Binding_Pre_Op --
   ---------------------------

   procedure Global_Binding_Pre_Op
     (State : in out Printer_State;
      Node  : W_Global_Binding_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Global_Binding_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Global_Binding_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Global_Binding_Get_Def (Node));
   end Global_Binding_Pre_Op;

   ----------------------------
   -- Global_Binding_Post_Op --
   ----------------------------

   procedure Global_Binding_Post_Op
     (State : in out Printer_State;
      Node  : W_Global_Binding_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Global_Binding_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Global_Binding_Get_Binders (Node));
      --  Traverse
      --    (State,
      --     Global_Binding_Get_Def (Node));
   end Global_Binding_Post_Op;

   -------------------------------
   -- Global_Rec_Binding_Pre_Op --
   -------------------------------

   procedure Global_Rec_Binding_Pre_Op
     (State : in out Printer_State;
      Node  : W_Global_Rec_Binding_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Global_Rec_Binding_Get_Name (Node));
   end Global_Rec_Binding_Pre_Op;

   --------------------------------
   -- Global_Rec_Binding_Post_Op --
   --------------------------------

   procedure Global_Rec_Binding_Post_Op
     (State : in out Printer_State;
      Node  : W_Global_Rec_Binding_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Global_Rec_Binding_Get_Name (Node));
   end Global_Rec_Binding_Post_Op;

   ----------------------------------
   -- Parameter_Declaration_Pre_Op --
   ----------------------------------

   procedure Parameter_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Parameter_Declaration_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Parameter_Declaration_Get_External (Node));
      --  Traverse_List
      --    (State,
      --     Parameter_Declaration_Get_Names (Node));
      --  Traverse_List
      --    (State,
      --     Parameter_Declaration_Get_Parameter_Type (Node));
   end Parameter_Declaration_Pre_Op;

   -----------------------------------
   -- Parameter_Declaration_Post_Op --
   -----------------------------------

   procedure Parameter_Declaration_Post_Op
     (State : in out Printer_State;
      Node  : W_Parameter_Declaration_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Parameter_Declaration_Get_External (Node));
      --  Traverse_List
      --    (State,
      --     Parameter_Declaration_Get_Names (Node));
      --  Traverse_List
      --    (State,
      --     Parameter_Declaration_Get_Parameter_Type (Node));
   end Parameter_Declaration_Post_Op;

   ----------------------------------
   -- Exception_Declaration_Pre_Op --
   ----------------------------------

   procedure Exception_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Exception_Declaration_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Exception_Declaration_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Exception_Declaration_Get_Parameter (Node));
   end Exception_Declaration_Pre_Op;

   -----------------------------------
   -- Exception_Declaration_Post_Op --
   -----------------------------------

   procedure Exception_Declaration_Post_Op
     (State : in out Printer_State;
      Node  : W_Exception_Declaration_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Exception_Declaration_Get_Name (Node));
      --  Traverse
      --    (State,
      --     Exception_Declaration_Get_Parameter (Node));
   end Exception_Declaration_Post_Op;

   ------------------------------
   -- Logic_Declaration_Pre_Op --
   ------------------------------

   procedure Logic_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Logic_Declaration_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Logic_Declaration_Get_Decl (Node));
   end Logic_Declaration_Pre_Op;

   -------------------------------
   -- Logic_Declaration_Post_Op --
   -------------------------------

   procedure Logic_Declaration_Post_Op
     (State : in out Printer_State;
      Node  : W_Logic_Declaration_Id)
   is
   begin
      raise Not_Implemented;

      --  Traverse
      --    (State,
      --     Logic_Declaration_Get_Decl (Node));
   end Logic_Declaration_Post_Op;

end Why.Atree.Sprint;
