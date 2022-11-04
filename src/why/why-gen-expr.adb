------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2022, AdaCore                     --
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

with Ada.Strings;                   use Ada.Strings;
with Ada.Strings.Unbounded;         use Ada.Strings.Unbounded;
with Ada.Strings.Fixed;
with Checks;                        use Checks;
with Common_Containers;             use Common_Containers;
with Errout;                        use Errout;
with Eval_Fat;
with Gnat2Why.Error_Messages;       use Gnat2Why.Error_Messages;
with Gnat2Why.Expr;                 use Gnat2Why.Expr;
with Gnat2Why.Subprograms;          use Gnat2Why.Subprograms;
with Gnat2Why.Subprograms.Pointers; use Gnat2Why.Subprograms.Pointers;
with GNATCOLL.Utils;                use GNATCOLL.Utils;
with Sinput;                        use Sinput;
with SPARK_Definition;              use SPARK_Definition;
with SPARK_Definition.Annotate;     use SPARK_Definition.Annotate;
with SPARK_Util.Types;              use SPARK_Util.Types;
with Stand;                         use Stand;
with Urealp;                        use Urealp;
with Why.Atree.Accessors;           use Why.Atree.Accessors;
with Why.Atree.Modules;             use Why.Atree.Modules;
with Why.Atree.Tables;              use Why.Atree.Tables;
with Why.Gen.Arrays;                use Why.Gen.Arrays;
with Why.Gen.Binders;               use Why.Gen.Binders;
with Why.Gen.Names;                 use Why.Gen.Names;
with Why.Gen.Init;                  use Why.Gen.Init;
with Why.Gen.Pointers;              use Why.Gen.Pointers;
with Why.Gen.Progs;                 use Why.Gen.Progs;
with Why.Gen.Records;               use Why.Gen.Records;
with Why.Gen.Scalars;               use Why.Gen.Scalars;
with Why.Gen.Terms;                 use Why.Gen.Terms;
with Why.Images;                    use Why.Images;

package body Why.Gen.Expr is

   function Args_For_Scalar_Dynamic_Property
     (Ty     : Entity_Id;
      Expr   : W_Expr_Id;
      Domain : EW_Terms;
      Params : Transformation_Params := Body_Params)
      return W_Expr_Array;
   --  Computes the arguments to be used for a call to the dynamic property
   --  of a scalar type.

   function Insert_Single_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      To       : W_Type_Id;
      Expr     : W_Expr_Id)
      return W_Expr_Id;
   --  Assuming that there is at most one step between To and From in the
   --  type hierarchy (i.e. that there exists a conversion from From
   --  to To; a counterexample would be two abstract types whose base
   --  types differ), insert the corresponding conversion.

   function Insert_Single_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      From     : W_Type_Id;
      To       : W_Type_Id;
      Expr     : W_Expr_Id)
      return W_Expr_Id;
   --  Same as above, except the From type is explicitly given. This is useful
   --  for conversions with fixed-point types, as the base type EW_Fixed does
   --  not allow retrieving the name of the appropriate conversion function,
   --  only the abstract fixed-point type allows it.

   function New_Located_String (Input : Source_Ptr) return String;
   --  Build a string that represents the source location of the source
   --  pointer.

   function New_Check_Label
     (Sloc   : Source_Ptr;
      Reason : VC_Kind;
      Id     : VC_Id)
      return Symbol;
   --  Returns a label that identifies the check for communication between
   --  gnat2why and gnatwhy3.

   function Is_Essentially_Void_List (L : Why_Node_List) return Boolean;
   --  @param a list of Why nodes
   --  @return True if all elements of the list are essentially void

   function Is_Void_List (L : Why_Node_List) return Boolean;
   --  @param a list of Why nodes
   --  @return True if all elements of the list are void

   function Compute_VC_Sloc
     (N         : Node_Id;
      Left_Most : Boolean := False)
      return Source_Ptr;
   --  @param N a node where a Check is located
   --  @param Left_Most whether the returned source_pointer should be oriented
   --    at the left_most of the tree rooted in N
   --  @return the source_pointer of node N, taking into account "Left_Most"
   --    argument and other special cases

   ---------------------
   -- Local Constants --
   ---------------------

   --  Nth roots of the usual modulus for machine integers are tabled so that
   --  they can be used in Check_No_Wrap_Around_Modular_Operation for the case
   --  of an exponentiation of a value of a modular type with No_Wrap_Around
   --  annotation. The nth roots of a modulus M are represented as an array
   --  mapping every exponent e to a root r such that
   --
   --    r ** e < M <= (r+1) ** e
   --
   --  We use strict inequality on the left here because we ultimately want to
   --  find the maximum value r which can be raised to the exponent e without
   --  overflowing. Because Uintp unit is not initialized during elaboration
   --  but by an explicit call to Initialize procedure, we need to similarly
   --  fill in the value of these tables and check that the values in these
   --  tables are correct in a procedure called Initialize_Tables_Nth_Roots
   --  called at the start of gnat2why.

   type Roots is array (Natural range <>) of Uint
     with Predicate => Roots'First = 2;

   --  Nth roots of 2**8-1, rounded towards zero
   Roots_8_Bits   : Roots (2 .. 7) := (others => No_Uint);

   --  Nth roots of 2**16-1, rounded towards zero
   Roots_16_Bits  : Roots (2 .. 15) := (others => No_Uint);

   --  Nth roots of 2**32-1, rounded towards zero
   Roots_32_Bits  : Roots (2 .. 31) := (others => No_Uint);

   --  Nth roots of 2**64-1, rounded towards zero
   Roots_64_Bits  : Roots (2 .. 63) := (others => No_Uint);

   --  Nth roots of 2**128-1, rounded towards zero
   Roots_128_Bits : Roots (2 .. 127) := (others => No_Uint);

   Temp_Names_Map : Why_Node_Maps.Map := Why_Node_Maps.Empty_Map;

   -------------------
   -- Apply_Modulus --
   -------------------

   function Apply_Modulus
     (Op     : N_Op;
      E      : Type_Kind_Id;
      T      : W_Expr_Id;
      Domain : EW_Domain)
      return W_Expr_Id
   is
      Ty          : constant Type_Kind_Id := Retysp (E);
      Modulus_Val : Uint;
      BV_Type     : W_Type_Id;
   begin
      if Is_Modular_Integer_Type (Ty) and then Op /= N_Op_Divide then
         Modulus_Val := Modulus (Ty);
         BV_Type := Base_Why_Type (Ty);

         --  If the modulus matches the size of the machine integer (for
         --  example a modulus of 2 ** 32 for a 32-bits machine integer),
         --  no modulo operation is needed.

         if Modulus_Val = UI_Expon (2, Modular_Size (Ty)) then
            return T;

         --  Otherwise we perform the modulo on bitvectors

         else
            return New_Call (Name   => MF_BVs (BV_Type).Urem,
                             Domain => Domain,
                             Args   => (1 => T,
                                        2 => New_Modular_Constant
                                               (Value => Modulus_Val,
                                                Typ   => BV_Type)),
                             Typ    => BV_Type);
         end if;

      else
         return T;
      end if;
   end Apply_Modulus;

   --------------------------------------
   -- Args_For_Scalar_Dynamic_Property --
   --------------------------------------

   function Args_For_Scalar_Dynamic_Property
     (Ty     : Entity_Id;
      Expr   : W_Expr_Id;
      Domain : EW_Terms;
      Params : Transformation_Params := Body_Params)
      return W_Expr_Array
   is
   begin
      return (1 => New_Attribute_Expr
                 (Ty     => Ty,
                  Domain => Domain,
                  Attr   => Attribute_First,
                  Params => Params),
              2 => New_Attribute_Expr
                   (Ty     => Ty,
                    Domain => Domain,
                    Attr   => Attribute_Last,
                    Params => Params),
              3 =>
                Insert_Simple_Conversion
                  (Ada_Node => Ty,
                   Domain   => Domain,
                   Expr     => Expr,
                   To       => Base_Why_Type (Ty)));
   end Args_For_Scalar_Dynamic_Property;

   ----------------------
   -- Binding_For_Temp --
   ----------------------

   function Binding_For_Temp
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Tmp      : W_Expr_Id;
      Context  : W_Expr_Id)
     return W_Expr_Id
   is
      use Why_Node_Maps;
      C : Why_Node_Maps.Cursor := Temp_Names_Map.Find (+Tmp);
   begin

      --  if Tmp is in the map, we really introduced a temp variable and need
      --  to build a binding now.

      if Has_Element (C) then
         declare
            E : constant W_Expr_Id := +Element (C);
         begin
            --  we delete the entry, so that the map doesn't grow too much.

            Temp_Names_Map.Delete (C);

            return
              New_Typed_Binding
                (Ada_Node => Ada_Node,
                 Domain   => Domain,
                 Name     => +Tmp,
                 Def      => E,
                 Context  => Context);
         end;

      else
         --  Otherwise Tmp is not a temp associated with an expression.
         --  Presumably, no temp variable was actually created for it during
         --  a call of New_Temp_For_Expr. We just return the context.

         return Context;
      end if;
   end Binding_For_Temp;

   --------------------------
   -- Boolean_Expr_Of_Pred --
   --------------------------

   function Boolean_Expr_Of_Pred
     (W      : W_Pred_Id;
      Domain : EW_Domain)
      return W_Expr_Id
   is
   begin
      case Domain is
         when EW_Prog | EW_Pterm => return +Boolean_Prog_Of_Pred (W);
         when EW_Term            => return +Boolean_Term_Of_Pred (W);
         when EW_Pred            => return +W;
      end case;
   end Boolean_Expr_Of_Pred;

   --------------------------
   -- Boolean_Prog_Of_Pred --
   --------------------------

   function Boolean_Prog_Of_Pred (W : W_Pred_Id) return W_Prog_Id is
     (New_Any_Expr (Post        =>
                      New_Connection
                        (Left  =>
                           New_Call (Name   => Why_Eq,
                                     Typ    => EW_Bool_Type,
                                     Args   =>
                                       (+New_Result_Ident (EW_Bool_Type),
                                        +True_Term)),
                         Op    => EW_Equivalent,
                         Right => W),
                    Labels      => Symbol_Sets.Empty_Set,
                    Return_Type => EW_Bool_Type));

   --------------------------
   -- Boolean_Term_Of_Pred --
   --------------------------

   function Boolean_Term_Of_Pred (W : W_Pred_Id) return W_Term_Id is
     (+W_Expr_Id'(New_Conditional (Condition => +W,
                                   Then_Part => +True_Term,
                                   Else_Part => +False_Term,
                                   Typ       => EW_Bool_Type,
                                   Domain    => EW_Term)));

   --------------------------------------------
   -- Check_No_Wrap_Around_Modular_Operation --
   --------------------------------------------

   function Check_No_Wrap_Around_Modular_Operation
     (Ada_Node   : Node_Id;
      Ada_Type   : Type_Kind_Id;
      Op         : N_Op;
      Left_Opnd  : W_Expr_Id := Why_Empty;
      Right_Opnd : W_Expr_Id;
      Rep_Type   : W_Type_Id;
      Modulus    : Uint)
      return W_Prog_Id
   is
   begin
      --  Negation of a modular value does not overflow iff the value is zero

      if Op = N_Op_Minus then
         declare
            Right_Expr : constant W_Term_Id := New_Temp_For_Expr (Right_Opnd);
            Zero_Expr  : constant W_Term_Id :=
              New_Modular_Constant (Value => Uint_0,
                                    Typ   => Rep_Type);
            Check : constant W_Prog_Id :=
              New_Ignore (Prog =>
                            New_Located_Assert (Ada_Node,
                              New_Comparison (Symbol => Why_Eq,
                                              Left   => Right_Expr,
                                              Right  => Zero_Expr),
                              VC_Overflow_Check,
                              EW_Assert));
         begin
            return Binding_For_Temp (Tmp     => Right_Expr,
                                     Context => Check);
         end;

      --  Exponential value ** expon does not overflow if
      --    . expon is zero or one, or
      --    . value is zero or one, or
      --    . for value n of expon, value is less than the nth root of the
      --      modulus (to avoid an overflow when computing the exponential in
      --      the underlying machine integer) and the result is less than this
      --      modulus.
      --
      --  The overall check is thus:
      --
      --      ( expon = 0 \/ expon = 1 \/
      --        value = 0 \/ value = 1 \/
      --        (expon = 2 /\ value <= roots (2)) \/ ...) )
      --      /\ value ** expon < modulus

      elsif Op = N_Op_Expon then
         declare
            function Select_Roots return Roots is
              (if    Rep_Type = EW_BitVector_8_Type   then Roots_8_Bits
               elsif Rep_Type = EW_BitVector_16_Type  then Roots_16_Bits
               elsif Rep_Type = EW_BitVector_32_Type  then Roots_32_Bits
               elsif Rep_Type = EW_BitVector_64_Type  then Roots_64_Bits
               elsif Rep_Type = EW_BitVector_128_Type then Roots_128_Bits
               else raise Program_Error);

            function Rep_Modulus return Uint is
              (if    Rep_Type = EW_BitVector_8_Type   then Uint_2 ** 8
               elsif Rep_Type = EW_BitVector_16_Type  then Uint_2 ** 16
               elsif Rep_Type = EW_BitVector_32_Type  then Uint_2 ** 32
               elsif Rep_Type = EW_BitVector_64_Type  then Uint_2 ** 64
               elsif Rep_Type = EW_BitVector_128_Type then Uint_2 ** 128
               else raise Program_Error);

            Value_Expr : constant W_Term_Id := New_Temp_For_Expr (Left_Opnd);
            Expon_Expr : constant W_Term_Id := New_Temp_For_Expr (Right_Opnd);
            Nth_Roots  : constant Roots := Select_Roots;
            Oper_Expr  : constant W_Term_Id :=
              New_Call (Ada_Node => Ada_Node,
                        Name     => MF_BVs (Rep_Type).Power,
                        Args     => (1 => +Value_Expr,
                                     2 => +Expon_Expr),
                        Typ      => Rep_Type);
            Check     : W_Pred_Id;
            Do_Check  : W_Prog_Id;

         begin
            --  There is no overflow if the exponent is zero or one, or if the
            --  value is zero or one.

            Check := New_Or_Pred
              ((1 => New_Comparison
                 (Symbol => Why_Eq,
                  Left   => Expon_Expr,
                  Right  => New_Integer_Constant (Value => Uint_0)),
                2 => New_Comparison
                 (Symbol => Why_Eq,
                  Left   => Expon_Expr,
                  Right  => New_Integer_Constant (Value => Uint_1)),
                3 => New_Comparison
                 (Symbol => Why_Eq,
                  Left   => Value_Expr,
                  Right  => New_Modular_Constant
                    (Value => Uint_0, Typ => Rep_Type)),
                4 => New_Comparison
                 (Symbol => Why_Eq,
                  Left   => Value_Expr,
                  Right  => New_Modular_Constant
                    (Value => Uint_1, Typ => Rep_Type))));

            --  For other values of exponents, check that the value being
            --  raised to this exponent is less or equal to the maximum
            --  value which leads to a result in bounds for that bitvector.

            for Expon in Nth_Roots'Range loop
               Check := New_Or_Pred
                 (Left   => New_And_Pred
                    (Left   => New_Comparison
                       (Symbol => Why_Eq,
                        Left   => Expon_Expr,
                        Right  => New_Integer_Constant
                          (Value => UI_From_Int (Int (Expon)))),
                     Right  => New_Comparison
                       (Symbol => MF_BVs (Rep_Type).Ule,
                        Left   => Value_Expr,
                        Right  => New_Modular_Constant
                          (Value => Nth_Roots (Expon),
                           Typ   => Rep_Type))),
                  Right  => Check);
            end loop;

            --  Now check also that the result is less than the value of
            --  modulus, in case the modulus is smaller than the full range
            --  of the bitvector.

            if Modulus /= Rep_Modulus then
               declare
                  Modulus_Expr : constant W_Term_Id :=
                    New_Modular_Constant (Value => Modulus,
                                          Typ   => Rep_Type);
               begin
                  Check := New_And_Pred
                    (Left   => Check,
                     Right  => New_Comparison
                       (Symbol => MF_BVs (Rep_Type).Ult,
                        Left   => Oper_Expr,
                        Right  => Modulus_Expr));
               end;
            end if;

            Do_Check := New_Ignore (Prog =>
                                      New_Located_Assert (Ada_Node,
                                        Check,
                                        VC_Overflow_Check,
                                        EW_Assert));
            Do_Check := Binding_For_Temp (Tmp     => Expon_Expr,
                                          Context => Do_Check);
            return Binding_For_Temp (Tmp     => Value_Expr,
                                     Context => Do_Check);
         end;

      --  For binary operations, go to a suitably large bitvector for computing
      --  the result, then check it is strictly lower than the modulus.

      else
         declare
            Left_Expr  : constant W_Term_Id := New_Temp_For_Expr (Left_Opnd);
            Right_Expr : constant W_Term_Id := New_Temp_For_Expr (Right_Opnd);

            Next_Bv      : constant W_Type_Id :=
              (if Modulus <= UI_Expon (2, 8) then
                 (if Modular_Size (Ada_Type) < 16 then EW_BitVector_16_Type
                  else Rep_Type)
               elsif Modulus <= UI_Expon (2, 16) then
                 (if Modular_Size (Ada_Type) < 32 then EW_BitVector_32_Type
                  else Rep_Type)
               elsif Modulus <= UI_Expon (2, 32) then
                 (if Modular_Size (Ada_Type) < 64 then EW_BitVector_64_Type
                  else Rep_Type)
               elsif Modulus <= UI_Expon (2, 64) then
                 (if Modular_Size (Ada_Type) < 128 then EW_BitVector_128_Type
                  else Rep_Type)
               else
                  EW_BitVector_256_Type);
            Modulus_Expr : constant W_Term_Id :=
              New_Modular_Constant (Value => Modulus,
                                    Typ   => Next_Bv);
            Next_Left    : constant W_Term_Id :=
              Insert_Simple_Conversion (Expr => Left_Expr,
                                        To   => Next_Bv);
            Next_Right   : constant W_Term_Id :=
              Insert_Simple_Conversion (Expr => Right_Expr,
                                        To   => Next_Bv);
            Oper         : constant W_Identifier_Id :=
              (case Op is
                 when N_Op_Add      => MF_BVs (Next_Bv).Add,
                 when N_Op_Subtract => MF_BVs (Next_Bv).Sub,
                 when N_Op_Multiply => MF_BVs (Next_Bv).Mult,
                 when others        => raise Program_Error);
            Oper_Expr     : constant W_Term_Id :=
              New_Call (Ada_Node => Ada_Node,
                        Name     => Oper,
                        Args     => (1 => +Next_Left,
                                     2 => +Next_Right),
                        Typ      => Next_Bv);
            Check : constant W_Prog_Id :=
              New_Ignore (Prog =>
                            New_Located_Assert (Ada_Node,
                              New_Comparison (Symbol => MF_BVs (Next_Bv).Ult,
                                              Left   => Oper_Expr,
                                              Right  => Modulus_Expr),
                              VC_Overflow_Check,
                              EW_Assert));
         begin
            return Binding_For_Temp
              (Tmp     => Left_Expr,
               Context =>
                 Binding_For_Temp (Tmp     => Right_Expr,
                                   Context => Check));
         end;
      end if;
   end Check_No_Wrap_Around_Modular_Operation;

   ---------------------
   -- Compute_VC_Sloc --
   ---------------------

   function Compute_VC_Sloc
     (N         : Node_Id;
      Left_Most : Boolean := False)
      return Source_Ptr
   is
      Slc : Source_Ptr;
   begin
      --  For VCs, we mostly want to point directly to the relevant node [N].
      --  For other nodes (e.g. pretty printing labels) it's more sensible to
      --  point to the beginning of the expression instead of the operator.
      --  This is achieved by calling [First_Sloc] instead of [Sloc]. However,
      --  [First_Sloc] does not work for N_And_Then nodes in assertions which
      --  are rewritten in a strange manner, so we do not do this optimization
      --  in that case. See also [New_Pretty_Label].

      if not Left_Most
            or else
         (Comes_From_Source (N)
           and then Is_Rewrite_Substitution (N)
           and then Nkind (Original_Node (N)) = N_And_Then)
      then
         Slc := Sloc (N);
      else
         Slc := Safe_First_Sloc (N);
      end if;
      return Slc;
   end Compute_VC_Sloc;

   --------------
   -- Get_Type --
   --------------

   function Get_Type (E : W_Expr_Id) return W_Type_Id is
   begin
      case Get_Kind (+E) is
         when W_Integer_Constant =>
            return EW_Int_Type;

         when W_Fixed_Constant =>
            return +Get_Typ (W_Fixed_Constant_Id (E));

         when W_Real_Constant =>
            return EW_Real_Type;

         when W_Float_Constant =>
            return +Get_Typ (W_Float_Constant_Id (E));

         when W_Range_Constant =>
            return +Get_Typ (W_Range_Constant_Id (E));

         when W_Modular_Constant =>
            return +Get_Typ (W_Modular_Constant_Id (E));

         when W_Literal =>
            return EW_Bool_Type;

         when W_Loop
            | W_Assignment
            | W_Assert
         =>
            return EW_Unit_Type;

         when W_Connection
            | W_Not
            | W_Universal_Quantif
            | W_Existential_Quantif
         =>
            return EW_Bool_Type;

         when W_Identifier =>
            return Get_Typ (W_Identifier_Id (E));

         when W_Tagged =>
            return Get_Typ (W_Tagged_Id (E));

         when W_Call =>
            return Get_Typ (W_Call_Id (E));

         when W_Binding =>
            if Get_Typ (W_Binding_Id (E)) = Why_Empty then
               return Get_Type (Get_Context (W_Binding_Id (E)));
            else
               return Get_Typ (W_Binding_Id (E));
            end if;

         when W_Elsif =>
            return Get_Typ (W_Elsif_Id (E));

         when W_Conditional =>
            return Get_Typ (W_Conditional_Id (E));

         when W_Deref =>
            return Get_Typ (W_Deref_Id (E));

         when W_Record_Access =>
            return Get_Typ (W_Record_Access_Id (E));

         when W_Record_Update =>
            return Get_Typ (W_Record_Update_Id (E));

         when W_Record_Aggregate =>
            return Get_Typ (W_Record_Aggregate_Id (E));

         when W_Binding_Ref =>
            return Get_Typ (W_Binding_Ref_Id (E));

         when W_Any_Expr =>
            return Get_Return_Type (W_Any_Expr_Id (E));

         when W_Abstract_Expr =>
            return Get_Typ (W_Abstract_Expr_Id (E));

         when W_Try_Block =>
            return Get_Typ (W_Try_Block_Id (E));

         when W_Raise =>
            return Get_Typ (W_Raise_Id (E));

         when W_Label =>
            return Get_Typ (W_Label_Id (E));

         when W_Loc_Label =>
            return Get_Type (Get_Def (W_Loc_Label_Id (E)));

         when W_Epsilon =>
            return Get_Typ (W_Epsilon_Id (E));

         --  ??? The following nodes should get their own Type field at some
         --  point, right now we use recursion.

         when W_Statement_Sequence =>
            declare
               use Why_Node_Lists;
               L : constant List :=
                 Get_List (+Get_Statements (W_Statement_Sequence_Id (E)));
            begin
               return Get_Type (+Last_Element (L));
            end;

         when others =>
            return Why_Empty;
      end case;

   end Get_Type;

   ---------------------------------
   -- Initialize_Tables_Nth_Roots --
   ---------------------------------

   procedure Initialize_Tables_Nth_Roots is

      procedure Check_Roots (Modulus : Uint; R : Roots) with Ghost;
      --  Check that the tabled values of nth roots R for Modulus are correct

      procedure Check_Roots (Modulus : Uint; R : Roots) is
      begin
         for Expon in R'Range loop
            declare
               Pow  : constant Uint := R (Expon) ** Int (Expon);
               Next : constant Uint := (R (Expon) + 1) ** Int (Expon);
            begin
               pragma Assert (Pow < Modulus and Modulus <= Next);
            end;
         end loop;
      end Check_Roots;

      function UI is new Uintp.UI_From_Integral (Long_Long_Integer);
      --  Take literal inputs up to 2**63 - 1 below. Use Long_Long_Integer
      --  which is 64-bits in GNAT for native platforms, to minimize tricks to
      --  just the value 2**64 - 1, which needs to be expressed based on the
      --  converted value of 2**63 - 1.

   --  Start of processing for Initialize_Tables_Nth_Roots

   begin
      Roots_8_Bits :=
        (2     => UI (15),
         3     => UI (6),
         4 | 5 => UI (3),
         6 | 7 => UI (2));

      Check_Roots (Uint_2 ** 8, Roots_8_Bits);

      Roots_16_Bits :=
        (2        => UI (255),
         3        => UI (40),
         4        => UI (15),
         5        => UI (9),
         6        => UI (6),
         7        => UI (4),
         8  .. 10 => UI (3),
         11 .. 15 => UI (2));

      Check_Roots (Uint_2 ** 16, Roots_16_Bits);

      Roots_32_Bits :=
        (2        => UI (65_535),
         3        => UI (1625),
         4        => UI (255),
         5        => UI (84),
         6        => UI (40),
         7        => UI (23),
         8        => UI (15),
         9        => UI (11),
         10       => UI (9),
         11       => UI (7),
         12       => UI (6),
         13       => UI (5),
         14 .. 15 => UI (4),
         16 .. 20 => UI (3),
         21 .. 31 => UI (2));

      Check_Roots (Uint_2 ** 32, Roots_32_Bits);

      Roots_64_Bits :=
        (2        => UI (2**32 - 1),
         3        => UI (2_642_245),
         4        => UI (65_535),
         5        => UI (7131),
         6        => UI (1625),
         7        => UI (565),
         8        => UI (255),
         9        => UI (138),
         10       => UI (84),
         11       => UI (56),
         12       => UI (40),
         13       => UI (30),
         14       => UI (23),
         15       => UI (19),
         16       => UI (15),
         17       => UI (13),
         18       => UI (11),
         19       => UI (10),
         20       => UI (9),
         21       => UI (8),
         22       => UI (7),
         23 .. 24 => UI (6),
         25 .. 27 => UI (5),
         28 .. 31 => UI (4),
         32 .. 40 => UI (3),
         41 .. 63 => UI (2));

      Check_Roots (Uint_2 ** 64, Roots_64_Bits);

      Roots_128_Bits :=
        (2         => UI (2**63 - 1) * 2 + 1,
         3         => UI (6_981_463_658_331),
         4         => UI (2**32 - 1),
         5         => UI (50_859_008),
         6         => UI (2_642_245),
         7         => UI (319_557),
         8         => UI (65_535),
         9         => UI (19_112),
         10        => UI (7131),
         11        => UI (3183),
         12        => UI (1625),
         13        => UI (920),
         14        => UI (565),
         15        => UI (370),
         16        => UI (255),
         17        => UI (184),
         18        => UI (138),
         19        => UI (106),
         20        => UI (84),
         21        => UI (68),
         22        => UI (56),
         23        => UI (47),
         24        => UI (40),
         25        => UI (34),
         26        => UI (30),
         27        => UI (26),
         28        => UI (23),
         29        => UI (21),
         30        => UI (19),
         31        => UI (17),
         32        => UI (15),
         33        => UI (14),
         34        => UI (13),
         35        => UI (12),
         36 .. 37  => UI (11),
         38        => UI (10),
         39 .. 40  => UI (9),
         41 .. 42  => UI (8),
         43 .. 45  => UI (7),
         46 .. 49  => UI (6),
         50 .. 55  => UI (5),
         56 .. 63  => UI (4),
         64 .. 80  => UI (3),
         81 .. 127 => UI (2));

      Check_Roots (Uint_2 ** 128, Roots_128_Bits);

   end Initialize_Tables_Nth_Roots;

   -----------------------------
   -- Insert_Array_Conversion --
   -----------------------------

   function Insert_Array_Conversion
     (Domain         : EW_Domain;
      Ada_Node       : Node_Id := Empty;
      Expr           : W_Expr_Id;
      To             : W_Type_Id;
      Need_Check     : Boolean := False;
      Force_No_Slide : Boolean := False;
      Is_Qualif      : Boolean := False;
      No_Init        : Boolean := False)
      return W_Expr_Id
   is
      From      : constant W_Type_Id := Get_Type (Expr);
      To_Ent    : constant Entity_Id := Get_Ada_Node (+To);
      From_Ent  : constant Entity_Id := Get_Ada_Node (+From);
      Dim       : constant Positive := Positive (Number_Dimensions (To_Ent));

      function Insert_Array_Index_Check
        (Expr   : W_Term_Id;
         To_Ent : Entity_Id)
         return W_Prog_Id;

      function Insert_Length_Check
        (Expr   : W_Term_Id;
         To_Ent : Entity_Id)
         return W_Prog_Id;

      function Insert_Array_Range_Check
        (Expr   : W_Term_Id;
         To_Ent : Entity_Id)
         return W_Prog_Id;

      ------------------------------
      -- Insert_Array_Range_Check --
      ------------------------------

      function Insert_Array_Range_Check
        (Expr   : W_Term_Id;
         To_Ent : Entity_Id)
         return W_Prog_Id
      is
         Check : W_Pred_Id;

      begin
         pragma Assert (not Is_Static_Array_Type (To_Ent));

         --  For dynamic types, use dynamic_property

         Check := +New_Dynamic_Property
           (Domain => EW_Pred,
            Ty     => To_Ent,
            Expr   => Expr);

         return New_Located_Assert (Ada_Node,
                                    Check,
                                    VC_Range_Check,
                                    EW_Assert);
      end Insert_Array_Range_Check;

      ------------------------------
      -- Insert_Array_Index_Check --
      ------------------------------

      function Insert_Array_Index_Check
        (Expr   : W_Term_Id;
         To_Ent : Entity_Id)
         return W_Prog_Id
      is
         Constrained : constant Boolean := Is_Constrained (To_Ent);
         Check       : W_Pred_Id;
         Dim         : constant Positive :=
           Positive (Number_Dimensions (To_Ent));
         Eqs         : W_Pred_Array (1 .. 2 * Dim);
         Count       : Natural := 0;
         Check_Info  : Check_Info_Type := New_Check_Info;
      begin
         for I in 1 .. Dim loop

            --  If To_Ent is constrained or the current index has a fixed
            --  lower bound, add constraint on the first bound.

            if Constrained
              or else Is_Fixed_Lower_Bound_Index_Subtype
                (Nth_Index_Type (To_Ent, I))
            then
               Count := Count + 1;
               Eqs (Count) := New_Comparison
                 (Symbol => Why_Eq,
                  Left   => Get_Array_Attr
                    (Expr => Expr,
                     Attr => Attribute_First,
                     Dim  => I),
                  Right  => Get_Array_Attr
                    (Domain => EW_Term,
                     Attr   => Attribute_First,
                     Dim    => I,
                     Ty     => To_Ent));
            end if;

            --  If To_Ent is constrained add constraint on the last bound

            if Constrained then
               Count := Count + 1;
               Eqs (Count) := New_Comparison
                 (Symbol => Why_Eq,
                  Left   => Get_Array_Attr
                    (Expr => Expr,
                     Attr => Attribute_Last,
                     Dim  => I),
                  Right  => Get_Array_Attr
                    (Domain => EW_Term,
                     Attr   => Attribute_Last,
                     Dim    => I,
                     Ty     => To_Ent));
            end if;
         end loop;

         Check := New_And_Pred (Eqs (1 .. Count));

         --  For a simple one-dimensional array, record the index type used for
         --  the index check associated with the Ada node.

         if Dim = 1 then
            Check_Info.Fix_Info.Range_Check_Ty := Nth_Index_Type (To_Ent, 1);
         end if;

         return New_Located_Assert (Ada_Node,
                                    Check,
                                    VC_Index_Check,
                                    EW_Assert,
                                    Check_Info);
      end Insert_Array_Index_Check;

      -------------------------
      -- Insert_Length_Check --
      -------------------------

      function Insert_Length_Check
        (Expr   : W_Term_Id;
         To_Ent : Entity_Id)
         return W_Prog_Id
      is
         Check : constant W_Pred_Id :=
           New_Length_Equality
             (Left_Arr => Expr,
              Right    => To_Ent,
              Dim      => Positive (Number_Dimensions (To_Ent)));

      begin
         if Is_True_Boolean (+Check) then
            return +Void;
         else
            return
              New_Located_Assert (Ada_Node, Check, VC_Length_Check, EW_Assert);
         end if;
      end Insert_Length_Check;

      Need_Slide : constant Boolean := Needs_Slide (From_Ent, To_Ent);
      Sliding    : constant Boolean :=
        not Force_No_Slide and then Need_Slide and then not Is_Qualif;
      Arr_Init   : W_Expr_Id := Expr;
      Arr_Expr   : W_Term_Id;
      T          : W_Expr_Id;

      Pred_Check : constant Boolean :=
        Domain = EW_Prog
        and then not No_Init
        and then Need_Check
        and then Has_Predicates (Get_Ada_Node (+To))
        and then not Is_Call_Arg_To_Predicate_Function (Ada_Node);
      Init_Check : constant Boolean :=
        Domain = EW_Prog
        and then not No_Init
        and then Need_Check
        and then Is_Init_Wrapper_Type (From)
        and then not Is_Init_Wrapper_Type (To);

      On_Wrapper : constant Boolean :=
        Is_Init_Wrapper_Type (From)
        and Is_Init_Wrapper_Type (To);
      From_Split : constant W_Type_Id :=
        (if Is_Static_Array_Type (From_Ent) then From
         else EW_Split (From_Ent, Relaxed_Init => On_Wrapper));
      To_Split : constant W_Type_Id :=
        (if Is_Static_Array_Type (To_Ent) then To
         else EW_Split (To_Ent, Relaxed_Init => On_Wrapper));

   --  Beginning of processing for Insert_Array_Conversion

   begin
      if To_Ent = From_Ent
        and then Is_Init_Wrapper_Type (From) = Is_Init_Wrapper_Type (To)
      then

         --  No range check needed

         return Expr;
      end if;

      --  Check for initialization if needed. We also need an initialization
      --  check if we should check predicates.

      if Init_Check or else Pred_Check then
         Arr_Init := Insert_Initialization_Check
           (Ada_Node               => Ada_Node,
            E                      => From_Ent,
            Name                   => Arr_Init,
            Domain                 => Domain,
            Exclude_Always_Relaxed => True);
      end if;

      Arr_Expr := New_Temp_For_Expr (Arr_Init);

      --  1 - Put array in split form. If reconstruction is needed, also store
      --  appropriate bounds in Args.

      declare
         Args          : W_Expr_Array (1 .. 1 + 2 * Dim);
         Arg_Ind       : Positive := 1;

         Split_T       : W_Expr_Id;
         --  Placeholder to store the value of T before reconstruction. It is
         --  used to generate the predicate check.

         Need_Elt_Conv : constant Boolean :=
           Retysp (Component_Type (To_Ent)) /=
             Retysp (Component_Type (From_Ent));
         --  We need an element conversion if To and From do not have the
         --  same elements.

      begin
         --  Insert sliding if needed

         if Sliding then
            declare
               Args    : W_Expr_Array (1 .. 1 + 2 * Dim);
               Arg_Ind : Positive := 1;
               To_Idx  : Entity_Id := First_Index (To_Ent);
            begin
               Add_Map_Arg (Domain, Args, +Arr_Expr, Arg_Ind);
               for I in 1 .. Dim loop
                  Add_Attr_Arg
                    (Domain, Args, +Arr_Expr,
                     Attribute_First, I, Arg_Ind);

                  if Is_Constrained (To_Ent)
                    or else Is_Fixed_Lower_Bound_Index_Subtype (Etype (To_Idx))
                  then
                     Add_Attr_Arg
                       (Domain, Args, To_Ent,
                        Attribute_First, I, Arg_Ind);
                  else
                     Add_Attr_Arg
                       (Domain, Args, +Arr_Expr,
                        Attribute_First, I, Arg_Ind);
                  end if;

                  Next_Index (To_Idx);
               end loop;

               T := New_Call
                 (Domain => Domain,
                  Name   => Get_Array_Theory
                    (From_Ent, Is_Init_Wrapper_Type (From)).Slide,
                  Args   => Args,
                  Typ    => Get_Type (Args (1)));
            end;

            --  If To isn't a statically constrained array type, fill the Args
            --  array to allow reconstruction.
            --  Here, we must get attributes from the type as the slided
            --  expression has no registered bounds.

            if not Is_Static_Array_Type (To_Ent)  then
               Arg_Ind := 1;
               Add_Map_Arg (Domain, Args, T, Arg_Ind);

               for I in 1 .. Dim loop

                  --  If To_Ent is constrained or its Ith index has a fixed
                  --  lower bound, the index has been slided. Compute the
                  --  bounds from the expected type.

                  if Is_Constrained (To_Ent)
                    or else Is_Fixed_Lower_Bound_Index_Subtype
                      (Nth_Index_Type (To_Ent, I))
                  then

                     --  The first bound can be queried directly

                     Add_Attr_Arg
                       (Domain, Args, To_Ent,
                        Attribute_First, I, Arg_Ind);

                     --  If To_Ent is constrained the last bound can be queried
                     --  directly.

                     if Is_Constrained (To_Ent) then
                        Add_Attr_Arg
                          (Domain, Args, To_Ent,
                           Attribute_Last, I, Arg_Ind);

                     --  Otherwise, we recompute it from the first bound and
                     --  the length of the converted array. A range check might
                     --  be emitted if we are in the program domain.

                     else
                        declare
                           Target      : constant Entity_Id :=
                             Nth_Index_Type (To_Ent, I);
                           Length_Expr : constant W_Expr_Id :=
                             Build_Length_Expr (Domain, +Arr_Expr, I);
                           First_Expr  : constant W_Expr_Id :=
                             Args (Arg_Ind - 1);
                           Last_Expr   : constant W_Expr_Id := New_Discrete_Add
                             (Domain => Domain,
                              Left   => New_Discrete_Substract
                                (Domain => Domain,
                                 Left   => First_Expr,
                                 Right  => New_Discrete_Constant
                                   (Value => Uint_1, Typ => EW_Int_Type),
                                 Typ    => EW_Int_Type),
                              Right  => Length_Expr,
                              Typ    => EW_Int_Type);
                           --  Expression of the last index. Computation is
                           --  done on mathematical integers to avoid overflows
                           --  and wrap-arounds.

                        begin
                           --  Convert Last_Expr to the expected type

                           Args (Arg_Ind) :=
                             Insert_Simple_Conversion
                               (Domain => Domain,
                                Expr   => Last_Expr,
                                To     => Get_Type (First_Expr));

                           --  If we are in the EW_Prog domain, also introduce
                           --  a range check to make sure that Last_Expr is
                           --  in the expected type.

                           if Domain = EW_Prog and then Need_Check then
                              Args (Arg_Ind) := +Sequence
                                (New_Ignore
                                   (Ada_Node => Ada_Node,
                                    Prog     => New_Conditional
                                      (Ada_Node  => Ada_Node,
                                       Condition => +New_Comparison
                                         (Symbol => Int_Infix_Le,
                                          Domain => Domain,
                                          Left   => +Insert_Scalar_Conversion
                                            (Domain => Domain,
                                             Expr   => First_Expr,
                                             To     => EW_Int_Type),
                                          Right  => Last_Expr),
                                       Then_Part => Do_Range_Check
                                         (Ada_Node   => Ada_Node,
                                          Ty         => Target,
                                          W_Expr     => Last_Expr,
                                          Check_Kind => RCK_Range),
                                       Else_Part => Do_Range_Check
                                         (Ada_Node   => Ada_Node,
                                          Ty         => Base_Retysp (Target),
                                          W_Expr     => Last_Expr,
                                          Check_Kind => RCK_Range),
                                       Typ       => Get_Type (First_Expr))),
                                 +Args (Arg_Ind));
                           end if;

                           Arg_Ind := Arg_Ind + 1;
                        end;
                     end if;

                  --  The index has not been slided, we keep the bounds of the
                  --  converted expression.

                  else
                     Add_Attr_Arg
                       (Domain, Args, +Arr_Expr,
                        Attribute_First, I, Arg_Ind);
                     Add_Attr_Arg
                       (Domain, Args, +Arr_Expr,
                        Attribute_Last, I, Arg_Ind);
                  end if;
               end loop;
            end if;

         --  If reconstruction is needed, fill the Args array. T is the
         --  first element of Args.

         elsif not Is_Static_Array_Type (To_Ent) then
            Add_Array_Arg (Domain, Args, +Arr_Expr, Arg_Ind);
            T := Args (1);

         --  Both are statically constrained, T is Arr_Expr

         elsif Is_Static_Array_Type (From_Ent) then
            T := +Arr_Expr;

         --  To is in constrained but not From. Convert From to base.

         else
            T := Array_Convert_To_Base
              (Domain => Domain,
               Ar     => +Arr_Expr);
         end if;

         --  2. If From has relaxed initialization and we are not doing the
         --  conversion on init wrappers, add a conversion from the wrapper
         --  type.

         if Is_Init_Wrapper_Type (From) and then not On_Wrapper then
            T := New_Call
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Name     => Get_Array_Of_Wrapper_Name (From_Ent),
               Args     => (1 => T),
               Typ      => From_Split);
         end if;

         --  3. To_Ent and From_Ent do not have the same component type, apply
         --  the appropriate conversion.

         if Need_Elt_Conv then
            T := Insert_Single_Conversion
              (Ada_Node => Empty,
               Domain   => Domain,
               To       => To_Split,
               Expr     => T);

         --  No actual why call or conversion may have been inserted, but we
         --  still need to change the type of the Why AST node. We do that by
         --  adding a dummy node.

         else
            T := New_Label (Labels => Symbol_Sets.Empty_Set,
                            Def    => T,
                            Domain => Domain,
                            Typ    => To_Split);
         end if;

         --  Store the split value of T before attempting reconstruction. To
         --  avoid introducing duplicated checks, use a temporary.

         T := New_Temp_For_Expr (T);
         Split_T := T;

         --  4. If To has relaxed initialization and the conversion is not done
         --  on wrapper types, go to the wrapper now.

         if Is_Init_Wrapper_Type (To) and then not On_Wrapper then
            T := New_Call
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Name     => Get_Array_To_Wrapper_Name (To_Ent),
               Args     => (1 => T),
               Typ      => EW_Split (To_Ent, Relaxed_Init => True));
         end if;

         --  5. Reconstruct the array if needed

         if not Is_Static_Array_Type (To_Ent) then
            Args (1) := T;
            T :=
              New_Call
                (Domain => Domain,
                 Name   =>
                   E_Symb (To_Ent, WNE_Of_Array, Is_Init_Wrapper_Type (To)),
                 Args   => Args,
                 Typ    => To);
         end if;

         --  6. Insert length, range, index, and predicate check when necessary

         if Domain = EW_Prog and then Need_Check then
            declare
               Check_Type : constant Entity_Id := To_Ent;
            begin
               if Is_Qualif and then Need_Slide then
                  T := +Sequence
                    (Insert_Array_Index_Check (Arr_Expr, Check_Type),
                     +T);
               elsif Is_Constrained (Check_Type) then
                  T := +Sequence
                    (Insert_Length_Check (Arr_Expr, Check_Type),
                     +T);
               elsif not Sliding then
                  T := +Sequence
                    (Insert_Array_Range_Check (+Arr_Expr, Check_Type),
                     +T);
               else
                  --  For FLB types, the check that the last bound is in the
                  --  index type is performed during the sliding.

                  pragma Assert
                    (Is_Fixed_Lower_Bound_Array_Subtype (Check_Type));
               end if;

               --  If the target type has a direct or inherited predicate,
               --  generate a corresponding check. Do not generate a predicate
               --  check for an internal call to a parent predicate function
               --  inside the definition of a predicate function.

               if Pred_Check then

                  Args (1) := Split_T;

                  --  To apply the predicate check, we need to have initialized
                  --  values. Don't produce an initialization check, it was
                  --  done earlier.

                  if On_Wrapper then
                     pragma Assert (not Has_Relaxed_Init (To_Ent));
                     Args (1) := New_Call
                       (Ada_Node => Ada_Node,
                        Domain   => Domain,
                        Name     => Get_Array_Of_Wrapper_Name (To_Ent),
                        Args     => (1 => Args (1)),
                        Typ      =>
                          (if Is_Static_Array_Type (To_Ent)
                           then EW_Abstract (To_Ent)
                           else EW_Split (To_Ent)));
                  end if;

                  declare
                     Rec_Tmp : constant W_Expr_Id :=
                       (if not Is_Static_Array_Type (To_Ent)
                        then New_Call
                          (Domain => Domain,
                           Name   => E_Symb (To_Ent, WNE_Of_Array),
                           Args   => Args,
                           Typ    => EW_Abstract (To_Ent))
                        else Args (1));
                     --  If it is in split form, the array should be
                     --  reconstructed.
                  begin
                     T := +Sequence
                       (New_Predicate_Check (Ada_Node, Check_Type, Rec_Tmp),
                        +T);
                  end;
               end if;
            end;
         end if;

         T := Binding_For_Temp (Domain  => Domain,
                                Tmp     => Split_T,
                                Context => T);
      end;

      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => +Arr_Expr,
                             Context => T);

      return T;
   end Insert_Array_Conversion;

   -------------------------------
   -- Insert_Checked_Conversion --
   -------------------------------

   function Insert_Checked_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Expr     : W_Expr_Id;
      To       : W_Type_Id;
      Lvalue   : Boolean := False;
      No_Init  : Boolean := False)
      return W_Expr_Id
   is

      --  When converting between Ada types, detect cases where a check is not
      --  needed.

      From         : constant W_Type_Id := Get_Type (Expr);
      Check_Needed : Boolean;
      T            : W_Expr_Id := Expr;

   begin
      --  A string literal gets typed with a subtype of the expected type, even
      --  if it does not respect the associated predicate of the expected type.
      --  As a result, do not rely on the call to Check_Needed_On_Conversion in
      --  that case.
      --  If From has relaxed initialization and not To, we may need an
      --  initialization check.

      Check_Needed :=
        (if Get_Type_Kind (From) in EW_Abstract | EW_Split
           and then Get_Type_Kind (To) in EW_Abstract | EW_Split
           and then not (Nkind (Ada_Node) = N_String_Literal
                          and then Has_Predicates (Get_Ada_Node (+To)))
         then
            Check_Needed_On_Conversion (From => Get_Ada_Node (+From),
                                        To   => Get_Ada_Node (+To))
         or else
            Is_Choice_Of_Unconstrained_Array_Update (Ada_Node)
         or else (Is_Init_Wrapper_Type (From)
           and then not Is_Init_Wrapper_Type (To)
           and then not No_Init)
         else
            True);

      if Is_Private_Conversion (From, To)
        or else Is_Record_Conversion (From, To)
      then
         --  Conversion between record types need to go through their common
         --  root record type. A discriminant check may be needed. Currently
         --  perform it on all discriminant record types, as the flag
         --  Do_Discriminant_Check is not set appropriately by the frontend on
         --  type conversions.
         --  A tag check may also be needed if we convert from a classwide type
         --  to a type which is not an ancestor. As for the discriminant check,
         --  we always perform it.

         T := Insert_Record_Conversion (Domain     => Domain,
                                        Ada_Node   => Ada_Node,
                                        Expr       => T,
                                        To         => To,
                                        Need_Check => Check_Needed,
                                        No_Init    => No_Init);

      elsif Is_Array_Conversion (From, To) then
         --  The flag Do_Length_Check is not set consistently in the
         --  frontend, so check every array conversion.

         T := Insert_Array_Conversion (Domain     => Domain,
                                       Ada_Node   => Ada_Node,
                                       Expr       => T,
                                       To         => To,
                                       Need_Check => Check_Needed,
                                       No_Init    => No_Init);

      elsif Is_Subp_Pointer_Conversion (From, To) then
         T := Insert_Subp_Pointer_Conversion (Domain     => Domain,
                                              Ada_Node   => Ada_Node,
                                              Expr       => T,
                                              To         => To,
                                              Need_Check => Check_Needed,
                                              No_Init    => No_Init);

      elsif Is_Pointer_Conversion (From, To) then

         T := Insert_Pointer_Conversion (Domain     => Domain,
                                         Ada_Node   => Ada_Node,
                                         Expr       => T,
                                         To         => To,
                                         Need_Check => Check_Needed,
                                         No_Init    => No_Init);

      --  Conversion between scalar types

      else
         declare
            --  Flag for a range check; set if the expression node has
            --  Do_Range_Check flag set, if it is a type conversion whose flag
            --  Do_Overflow_Check is set. (See description of these flags in
            --  sinfo.ads for details.)

            --  Also, we special case a type conversion whose expression has a
            --  range check, when this appears as the actual of an out/in-out
            --  parameter of a call, because the current check machinery does
            --  not allow detecting the necessary check on the out copy.
            --  ??? It would be good if such special casing were closer to the
            --  code which handles the call

            Do_Check : constant Boolean :=
              Domain = EW_Prog and then Check_Needed and then
              Do_Check_On_Scalar_Conversion (Ada_Node);

         begin
            T := Insert_Scalar_Conversion (Domain   => Domain,
                                           Ada_Node => Ada_Node,
                                           Expr     => T,
                                           To       => To,
                                           Do_Check => Do_Check,
                                           Lvalue   => Lvalue,
                                           No_Init  => No_Init);
         end;
      end if;

      return T;
   end Insert_Checked_Conversion;

   ------------------------------
   -- Insert_Record_Conversion --
   ------------------------------

   function Insert_Record_Conversion
     (Ada_Node   : Node_Id;
      Domain     : EW_Domain;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False;
      No_Init    : Boolean := False)
      return W_Expr_Id
   is
      From   : constant W_Type_Id := Get_Type (Expr);
      --  Current result expression
      Result : W_Expr_Id := Expr;

      L : constant Node_Id := Get_Ada_Node (+From);
      R : constant Node_Id := Get_Ada_Node (+To);
      pragma Assert (Root_Retysp (L) = Root_Retysp (R));

      Need_Conv : constant Boolean :=
        Oldest_Parent_With_Same_Fields (L) /=
        Oldest_Parent_With_Same_Fields (R);

      Need_Discr_Check : constant Boolean :=
        Need_Check and then Count_Discriminants (R) > 0
        and then Is_Constrained (R);
      Need_Tag_Check   : constant Boolean :=
        Need_Check and then Is_Tagged_Type (R) and then not Is_Ancestor (R, L);

      --  Do not generate a predicate check for an internal call to a parent
      --  predicate function inside the definition of a predicate function.
      Need_Pred_Check : constant Boolean :=
        Need_Check
          and then not No_Init
          and then Has_Predicates (R)
          and then not Is_Call_Arg_To_Predicate_Function (Ada_Node);
      Check_Entity    : constant Entity_Id := Get_Ada_Node (+To);

      Base            : constant W_Type_Id :=
        EW_Abstract
          (Root_Retysp (L),
           Relaxed_Init => Is_Init_Wrapper_Type (From)
              and Is_Init_Wrapper_Type (To)
              and not Need_Pred_Check);
      pragma Assert (not Has_Relaxed_Init (R) or else not Need_Pred_Check);
      --  If To has predicate, the check must be done on initialized values

   begin
      --  The case where we are converting from an unchecked union type
      --  to a type without unchecked union should not occur as we do not
      --  support discriminants on derived type currently. If we were to
      --  support them, we would need to detect this case and emit a
      --  check message.

      pragma Assert (Is_Unchecked_Union (R) = Is_Unchecked_Union (L));

      --  If From has relaxed initialization and not Base, introduce a
      --  conversion and possibly a check.

      if Is_Init_Wrapper_Type (From)
        and then not Is_Init_Wrapper_Type (Base)
      then
         if Domain = EW_Prog and then not No_Init and then Need_Check then
            Result := Insert_Initialization_Check
              (Ada_Node               => Ada_Node,
               E                      => L,
               Name                   => Result,
               Domain                 => Domain,
               Exclude_Always_Relaxed => True);
         end if;
         Result := New_Call
           (Ada_Node => Ada_Node,
            Domain   => Domain,
            Name     => E_Symb (L, WNE_Of_Wrapper),
            Args     => (1 => Result),
            Typ      => EW_Abstract (L));
      end if;

      --  When From = To and no check needs to be inserted, do nothing

      if Need_Conv or else Need_Check then

         --  1. Convert From -> Base

         Result := Insert_Single_Conversion (Domain   => Domain,
                                             Ada_Node => Ada_Node,
                                             To       => Base,
                                             Expr     => Result);

         --  2. Possibly perform checks on root type

         if Domain = EW_Prog then

            --  2.a Possibly perform a discriminant check

            if Need_Discr_Check then
               Result := +Insert_Subtype_Discriminant_Check (Ada_Node,
                                                             Check_Entity,
                                                             +Result);
            end if;

            --  2.b Possibly perform a tag check

            if Need_Tag_Check then
               Result := +Insert_Tag_Check (Ada_Node,
                                            Check_Entity,
                                            +Result);
            end if;
         end if;

         --  3. Convert Base -> To

         Result := Insert_Single_Conversion
           (Domain   => Domain,
            Ada_Node => Ada_Node,
            To       =>
              (if Is_Init_Wrapper_Type (To)
               and then not Is_Init_Wrapper_Type (Base)
               then EW_Abstract (R)
               else To),
            Expr     => Result);

         --  4. Possibly perform a predicate check on target type To

         if Domain = EW_Prog
           and then Need_Pred_Check
         then
            Result := +Insert_Predicate_Check (Ada_Node,
                                               Check_Entity,
                                               +Result);
         end if;
      else
         Result := New_Label
           (Domain   => Domain,
            Labels   => Symbol_Sets.Empty_Set,
            Def      => Result,
            Typ      => EW_Abstract (R, Is_Init_Wrapper_Type (Base)));
      end if;

      --  If From has relaxed initialization and not Base, introduce a
      --  conversion.

      if Is_Init_Wrapper_Type (To)
        and then not Is_Init_Wrapper_Type (Base)
      then
         Result := New_Call
           (Ada_Node => Ada_Node,
            Domain   => Domain,
            Name     => E_Symb (R, WNE_To_Wrapper),
            Args     => (1 => Result),
            Typ      => To);
      end if;

      return Result;
   end Insert_Record_Conversion;

   -------------------------------
   -- Insert_Pointer_Conversion --
   -------------------------------

   function Insert_Pointer_Conversion
     (Ada_Node   : Node_Id;
      Domain     : EW_Domain;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False;
      No_Init    : Boolean := False)
      return W_Expr_Id
   is
      From   : constant W_Type_Id := Get_Type (Expr);
      --  Current result expression
      Result : W_Expr_Id := Expr;

      L : constant Node_Id := Get_Ada_Node (+From);
      R : constant Node_Id := Get_Ada_Node (+To);

      Need_Conv : constant Boolean :=
        Repr_Pointer_Type (L) /= Repr_Pointer_Type (R);
      pragma Assert (Root_Pointer_Type (L) = Root_Pointer_Type (R));

      Need_Not_Null_Check : constant Boolean := Can_Never_Be_Null (R);

      --  Do not generate a predicate check for an internal call to a parent
      --  predicate function inside the definition of a predicate function.

      Need_Pred_Check : constant Boolean :=
        not No_Init
        and then Has_Predicates (R)
        and then (No (Ada_Node)
                   or else Ada_Node not in N_Subexpr_Id
                   or else not Is_Call_Arg_To_Predicate_Function (Ada_Node));

   begin
      --  When neither checks nor conversions need to be inserted, return

      if not Need_Check and then not Need_Conv then
         return New_Label
           (Ada_Node => Ada_Node,
            Domain   => Domain,
            Labels   => Symbol_Sets.Empty_Set,
            Def      => Result,
            Typ      => To);
      end if;

      --  Conversion goes through the root type

      if Need_Conv then
         declare
            To_Base : constant W_Identifier_Id :=
              E_Symb (L, WNE_To_Base);
            Of_Base : constant W_Identifier_Id :=
              E_Symb (R, WNE_Of_Base);
         begin
            Result := New_Call
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Name     => To_Base,
               Args     => (1 => Result),
               Typ      => Get_Typ (To_Base));

            --  Insert subtype check on root type if needed

            if Need_Check and then Domain = EW_Prog then
               Result := +Insert_Pointer_Subtype_Check (Ada_Node,
                                                        R,
                                                        +Result);
            end if;

            Result := New_Call
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Name     => Of_Base,
               Args     => (1 => Result),
               Typ      => To);
         end;
      else
         Result := New_Label
           (Ada_Node => Ada_Node,
            Domain   => Domain,
            Labels   => Symbol_Sets.Empty_Set,
            Def      => Result,
            Typ      => To);
      end if;

      --  Predicate checks and null exclusion checks are performed after the
      --  conversion.

      if Need_Check and then Domain = EW_Prog then
         if Need_Pred_Check then
            Result := +Insert_Predicate_Check (Ada_Node,
                                               R,
                                               +Result);
         end if;

         if Need_Not_Null_Check then
            Result :=
              +New_VC_Call
              (Ada_Node => Ada_Node,
               Name     => To_Program_Space
                 (E_Symb (R, WNE_Assign_Null_Check)),
               Progs    => (1 => +Result),
               Reason   => VC_Null_Exclusion,
               Typ      => Get_Type (Result));
         end if;

      end if;

      return Result;
   end Insert_Pointer_Conversion;

   --------------------------
   -- Insert_Cnt_Loc_Label --
   --------------------------

   function Insert_Cnt_Loc_Label
     (Ada_Node     : Node_Id;
      E            : W_Expr_Id;
      Is_Loop_Head : Boolean := False)
      return W_Expr_Id
   is
   begin
      if Present (Ada_Node)
        and then Safe_First_Sloc (Ada_Node) > No_Location
      then
         declare
            --  This is intentionnally not generated in case of Implicit
            --  invariant (no explicit Loop_Invariant in the loop).
            Marker : constant Symbol :=
              (if Is_Loop_Head and then Nkind (Ada_Node) = N_Pragma then
                  NID ("Loop" & Node_Id'Image (Ada_Node))
               else
                  No_Symbol);
         begin
            return New_Loc_Label
              (Ada_Node     => Get_Ada_Node (+E),
               Sloc         => Safe_First_Sloc (Ada_Node),
               Domain       => Get_Domain (+E),
               Def          => E,
               Marker       => Marker);
         end;
      else
         return E;
      end if;
   end Insert_Cnt_Loc_Label;

   --------------------------------------
   -- Insert_Conversion_To_Rep_No_Bool --
   --------------------------------------

   function Insert_Conversion_To_Rep_No_Bool
     (Domain : EW_Domain;
      Expr : W_Expr_Id)
      return W_Expr_Id
   is
      Rep_Typ : constant W_Type_Id := Base_Why_Type_No_Bool (Expr);
   begin
      return Insert_Simple_Conversion (Domain => Domain,
                                       Expr   => Expr,
                                       To     => Rep_Typ);
   end Insert_Conversion_To_Rep_No_Bool;

   --------------------
   -- Do_Index_Check --
   --------------------

   function Do_Index_Check
     (Ada_Node : Node_Id;
      Arr_Expr : W_Term_Id;
      W_Expr   : W_Expr_Id;
      Dim      : Positive)
      return W_Prog_Id
   is
      Tmp        : constant W_Term_Id :=
        New_Temp_For_Expr (W_Expr);
      First_Expr : constant W_Term_Id :=
        Insert_Conversion_To_Rep_No_Bool (Expr => Get_Array_Attr
                                            (Expr => Arr_Expr,
                                             Attr => Attribute_First,
                                             Dim  => Dim));
      Last_Expr  : constant W_Term_Id :=
        Insert_Conversion_To_Rep_No_Bool (Expr => Get_Array_Attr
                                            (Expr => Arr_Expr,
                                             Attr => Attribute_Last,
                                             Dim  => Dim));

      Check_Info : Check_Info_Type := New_Check_Info;
      T          : W_Prog_Id;
   begin
      --  For arrays of dimension 1 only, record the index type used for the
      --  index check associated with the Ada node.

      if Number_Dimensions (Get_Ada_Node (+Get_Type (+Arr_Expr))) = 1 then
         Check_Info.Fix_Info.Range_Check_Ty :=
           Nth_Index_Type (Get_Ada_Node (+Get_Type (+Arr_Expr)), 1);
      end if;

      T := New_Located_Assert (Ada_Node   => Ada_Node,
                               Reason     => VC_Index_Check,
                               Pred       => New_Range_Expr
                                 (Low  => First_Expr,
                                  High => Last_Expr,
                                  Expr => Tmp),
                               Kind       => EW_Assert,
                               Check_Info => Check_Info);

      return Binding_For_Temp (Tmp     => Tmp,
                               Context => Sequence (T, +Tmp));
   end Do_Index_Check;

   --------------------
   -- Do_Range_Check --
   --------------------

   function Do_Range_Check
     (Ada_Node   : Node_Id;
      Ty         : Entity_Id;
      W_Expr     : W_Expr_Id;
      Check_Kind : Scalar_Check_Kind)
      return W_Prog_Id
   is
      Reason     : constant VC_Range_Kind := To_VC_Kind (Check_Kind);
      W_Type     : constant W_Type_Id :=
        (if Get_Type_Kind (Get_Type (W_Expr)) = EW_Split
         then Base_Why_Type (Get_Ada_Node (+Get_Type (W_Expr)))
         else Get_Type (W_Expr));
      Check_Info : constant Check_Info_Type :=
        New_Check_Info (Range_Check_Ty => Ty);
      --  Record the type used for the range check associated with the Ada node
      Result     : W_Prog_Id;
      W_Fun      : W_Identifier_Id;  --  range checking function

   begin
      --  When the range check comes from a modular type, either the expression
      --  is a bitvector and we apply the check on the largest bitvector type
      --  involved, or the expression is an int and we need to apply the check
      --  on int, as we don't know that the value of the expression fits in a
      --  bitvector.

      if Is_Modular_Integer_Type (Ty) then

         --  The type of expression is int, so we apply the range check on int

         if W_Type = EW_Int_Type then

            W_Fun := E_Symb (Ty, WNE_Range_Check_Fun_BV_Int);

            --  If the bounds are dynamic, we need to retrieve them for the
            --  check.

            if Type_Is_Modeled_As_Base (Ty) then
               declare
                  --  Convert first and last bounds from bitvector to int
                  W_First : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Ada_Node => Ty,
                       Domain   => EW_Term,
                       Expr     =>
                         New_Attribute_Expr (Ty     => Ty,
                                             Domain => EW_Term,
                                             Attr   => Attribute_First,
                                             Params => Body_Params),
                       To       => EW_Int_Type);
                  W_Last : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Ada_Node => Ty,
                       Domain   => EW_Term,
                       Expr     =>
                         New_Attribute_Expr (Ty     => Ty,
                                             Domain => EW_Term,
                                             Attr   => Attribute_Last,
                                             Params => Body_Params),
                       To       => EW_Int_Type);

                  --  Range check on int returns an int. To avoid converting it
                  --  back to bitvector which is harder for automatic provers,
                  --  save the bitvector value in a temporary to return later.
                  W_Tmp     : constant W_Expr_Id := New_Temp_For_Expr (W_Expr);
                  W_Int_Tmp : constant W_Expr_Id :=
                    Insert_Simple_Conversion (Ada_Node => Ty,
                                              Domain   => EW_Term,
                                              Expr     => W_Tmp,
                                              To       => EW_Int_Type);
               begin
                  Result :=
                    New_VC_Call (Ada_Node   => Ada_Node,
                                 Name       => W_Fun,
                                 Progs      => (1 => W_First,
                                                2 => W_Last,
                                                3 => W_Int_Tmp),
                                 Reason     => Reason,
                                 Check_Info => Check_Info,
                                 Typ        => Get_Typ (W_Fun));
                  Result :=
                    +Binding_For_Temp (Domain  => EW_Prog,
                                       Tmp     => W_Tmp,
                                       Context =>
                                         New_Binding
                                           (Domain   => EW_Prog,
                                            Name     =>
                                              New_Identifier (Name => "_"),
                                            Def      => +Result,
                                            Context  => +W_Tmp,
                                            Typ      => Get_Type (W_Expr)));
               end;

            --  If the bounds are static, the range checking function knows
            --  them, simply call it.

            else
               Result := New_VC_Call (Ada_Node   => Ada_Node,
                                      Name       => W_Fun,
                                      Progs      => (1 => +W_Expr),
                                      Reason     => Reason,
                                      Check_Info => Check_Info,
                                      Typ        => Get_Type (W_Expr));
            end if;

         elsif Why_Type_Is_Float (W_Type) then

            --  In the case of a conversion of a float into a bitvector, we
            --  perform the range check with floats by converting the bounds
            --  of the bitvector range into float and rounding W_Expr to the
            --  nearest integer (RNA). For this to be correct the first element
            --  of the range needs to be converted towards +infinity (RTP) and
            --  the last element towards -infinity (RTN).

            W_Fun := MF_Floats (W_Type).Range_Check;

            declare
               BV_Size : constant Uint := Modular_Size (Ty);

               Of_BV_RTP : constant W_Identifier_Id :=
                 (if BV_Size = Uint_8 then
                     MF_Floats (W_Type).Of_BV8_RTP
                  elsif BV_Size = Uint_16 then
                     MF_Floats (W_Type).Of_BV16_RTP
                  elsif BV_Size = Uint_32 then
                     MF_Floats (W_Type).Of_BV32_RTP
                  elsif BV_Size = Uint_64 then
                     MF_Floats (W_Type).Of_BV64_RTP
                  else
                     raise Program_Error);

               Of_BV_RTN : constant W_Identifier_Id :=
                 (if BV_Size = Uint_8 then
                     MF_Floats (W_Type).Of_BV8_RTN
                  elsif BV_Size = Uint_16 then
                     MF_Floats (W_Type).Of_BV16_RTN
                  elsif BV_Size = Uint_32 then
                     MF_Floats (W_Type).Of_BV32_RTN
                  elsif BV_Size = Uint_64 then
                     MF_Floats (W_Type).Of_BV64_RTN
                  else
                     raise Program_Error);

               --  Convert first and last bounds from bitvector to float
               W_First : constant W_Expr_Id :=
                 New_Call (Domain => EW_Term,
                           Name   => Of_BV_RTP,
                           Args   =>
                             (1 => New_Attribute_Expr
                                  (Ty     => Ty,
                                   Domain => EW_Term,
                                   Attr   => Attribute_First,
                                   Params => Body_Params)),
                           Typ => W_Type);

               W_Last : constant W_Expr_Id :=
                 New_Call (Domain => EW_Term,
                           Name   => Of_BV_RTN,
                           Args   =>
                             (1 => New_Attribute_Expr
                                  (Ty     => Ty,
                                   Domain => EW_Term,
                                   Attr   => Attribute_Last,
                                   Params => Body_Params)),
                           Typ    => W_Type);

               W_Expr_Rounded : constant W_Expr_Id :=
                 New_Call (Domain => EW_Term,
                           Name   => MF_Floats (W_Type).Rounding,
                           Args   => (1 => W_Expr),
                           Typ    => W_Type);
            begin
               Result :=
                 New_VC_Call (Ada_Node   => Ada_Node,
                              Name       => W_Fun,
                              Progs      => (1 => W_First,
                                             2 => W_Last,
                                             3 => W_Expr_Rounded),
                              Reason     => Reason,
                              Check_Info => Check_Info,
                              Typ        => Get_Type (W_Expr));
            end;

         --  The type of expression is bitvector, so we apply the range check
         --  on the largest bitvector type involved.
         else
            pragma Assert (Why_Type_Is_BitVector (W_Type));

            W_Fun := Range_Check_Name (Ty, Check_Kind);

            --  If the bounds are dynamic, we need to retrieve them for the
            --  check, by calling Args_For_Scalar_Dynamic_Property.

            if Type_Is_Modeled_As_Base (Ty) then
               declare
                  W_Tmp  : constant W_Expr_Id := New_Temp_For_Expr (W_Expr);
                  W_Args : constant W_Expr_Array :=
                    Args_For_Scalar_Dynamic_Property (Ty, W_Tmp, EW_Pterm);
               begin
                  Result :=
                    New_VC_Call (Ada_Node   => Ada_Node,
                                 Name       => W_Fun,
                                 Progs      => W_Args,
                                 Reason     => Reason,
                                 Check_Info => Check_Info,
                                 Typ        => Get_Typ (W_Fun));
                  Result :=
                    +Binding_For_Temp (Domain  => EW_Prog,
                                       Tmp     => W_Tmp,
                                       Context =>
                                         New_Binding
                                           (Domain   => EW_Prog,
                                            Name     =>
                                              New_Identifier (Name => "_"),
                                            Def      => +Result,
                                            Context  => +W_Tmp,
                                            Typ      => Get_Type (W_Expr)));
               end;

            --  If the bounds are static, the range checking function knows
            --  them.

            --  When converting from a bitvector of a smaller size, the
            --  expression can be safely converted to the target bitvector
            --  and the range check performed in the target bitvector, we then
            --  convert back to W_Type.

            elsif BitVector_Type_Size (W_Type) <= Modular_Size (Ty) then
               declare
                  Range_Typ : constant W_Type_Id := Type_Of_Node (Ty);
               begin
                  Result := +Insert_Simple_Conversion
                    (Domain => EW_Prog,
                     Expr   =>
                       +New_VC_Call (Ada_Node   => Ada_Node,
                                     Name       => W_Fun,
                                     Progs      =>
                                       (1 => +Insert_Simple_Conversion
                                          (Domain => EW_Prog,
                                           Expr   => W_Expr,
                                           To     => Range_Typ)),
                                     Reason     => Reason,
                                     Check_Info => Check_Info,
                                     Typ        => Range_Typ),
                     To     => W_Type);
               end;

            --  When converting to a bitvector of a stricly smaller size, the
            --  range check must be performed on the expression before it is
            --  converted to the target bitvector. Instead, convert the bounds
            --  of the target type to the larger source bitvector.

            else
               declare
                  W_First : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain   => EW_Term,
                       Expr     =>
                         New_Attribute_Expr (Ty     => Ty,
                                             Domain => EW_Prog,
                                             Attr   => Attribute_First,
                                             Params => Body_Params),
                       To       => W_Type);
                  W_Last : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain   => EW_Term,
                       Expr     =>
                         New_Attribute_Expr (Ty     => Ty,
                                             Domain => EW_Prog,
                                             Attr   => Attribute_Last,
                                             Params => Body_Params),
                       To       => W_Type);
               begin
                  W_Fun := Get_Modular_Converter_Range_Check
                             (W_Type, Base_Why_Type (Ty));
                  Result := New_VC_Call (Ada_Node   => Ada_Node,
                                         Name       => W_Fun,
                                         Progs      => (1 => W_First,
                                                        2 => W_Last,
                                                        3 => +W_Expr),
                                         Reason     => Reason,
                                         Check_Info => Check_Info,
                                         Typ        => W_Type);
               end;
            end if;
         end if;

      --  Range check does not come from a modular type. Everything is done in
      --  the representation type, either int for scalar and fixed-point types
      --  or real for floating-point types.

      else
         W_Fun := Range_Check_Name (Ty, Check_Kind);

         --  If the bounds are dynamic, we need to retrieve them for the check,
         --  by calling Args_For_Scalar_Dynamic_Property.

         if Type_Is_Modeled_As_Base (Ty) then
            declare
               W_Tmp : constant W_Expr_Id := New_Temp_For_Expr (W_Expr);
               W_Args : constant W_Expr_Array :=
                 Args_For_Scalar_Dynamic_Property (Ty, W_Tmp, EW_Pterm);
            begin
               Result := New_VC_Call (Ada_Node   => Ada_Node,
                                      Name       => W_Fun,
                                      Progs      => W_Args,
                                      Reason     => Reason,
                                      Check_Info => Check_Info,
                                      Typ        => Get_Type (W_Expr));
               Result :=
                 +Binding_For_Temp (Domain  => EW_Prog,
                                    Tmp     => W_Tmp,
                                    Context => +Result);
            end;

         --  If the bounds are static, the range checking function knows them

         else
            Result := New_VC_Call (Ada_Node   => Ada_Node,
                                   Name       => W_Fun,
                                   Progs      => (1 => +W_Expr),
                                   Reason     => Reason,
                                   Check_Info => Check_Info,
                                   Typ        => Get_Type (W_Expr));
         end if;
      end if;

      return Result;
   end Do_Range_Check;

   ------------------------------
   -- Insert_Scalar_Conversion --
   ------------------------------

   function Insert_Scalar_Conversion
     (Domain   : EW_Domain;
      Ada_Node : Node_Id := Empty;
      Expr     : W_Expr_Id;
      To       : W_Type_Id;
      Do_Check : Boolean := False;
      Lvalue   : Boolean := False;
      No_Init  : Boolean := False)
      return W_Expr_Id
   is
      From : constant W_Type_Id := Get_Type (Expr);

      --  Do not generate a predicate check for an internal call to a parent
      --  predicate function inside the definition of a predicate function.
      Do_Predicate_Check : constant Boolean :=
        Present (Get_Ada_Node (+To))
          and then Has_Predicates (Get_Ada_Node (+To))
          and then Get_Ada_Node (+To) /= Get_Ada_Node (+From)
          and then not Is_Call_Arg_To_Predicate_Function (Ada_Node);

      --  Type and kind for the range check
      Range_Type : Entity_Id := Empty;
      Check_Kind : Scalar_Check_Kind := RCK_Range;

   --  Start of processing for Insert_Scalar_Conversion

   begin
      --  Do nothing when
      --  1. From = To, and
      --  2. no rounding needed, and
      --  3. no predicate check needed, and
      --  4. a) no range check needed, _or_
      --     b) check is flagged but the base type is the one reserved for
      --        Standard.Boolean, so check does not need to be inserted.
      --        (Other boolean types in Ada have a base type of EW_Int.)

      if Eq_Base (To, From)
        and then not Do_Predicate_Check
        and then (not Do_Check
                  or else To = EW_Bool_Type)
      then
         return Expr;
      end if;

      --  Retrieve range check information

      if Do_Check then
         Get_Range_Check_Info (Ada_Node, Lvalue, Range_Type, Check_Kind);
      end if;

      return Insert_Scalar_Conversion
        (Domain      => Domain,
         Ada_Node    => Ada_Node,
         Expr        => Expr,
         To          => To,
         Range_Type  => Range_Type,
         Check_Kind  => Check_Kind,
         Lvalue      => Lvalue,
         No_Init     => No_Init);
   end Insert_Scalar_Conversion;

   function Insert_Scalar_Conversion
     (Domain     : EW_Domain;
      Ada_Node   : Node_Id := Empty;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Range_Type : Entity_Id;
      Check_Kind : Scalar_Check_Kind;
      Lvalue     : Boolean := False;
      No_Init    : Boolean := False;
      Skip_Pred  : Boolean := False)
      return W_Expr_Id
   is
      From    : constant W_Type_Id := Get_Type (Expr);
      To_Conc : constant W_Type_Id :=
        (if not Is_Init_Wrapper_Type (To) then To
         elsif Get_Type_Kind (To) = EW_Abstract
         then EW_Abstract (Get_Ada_Node (+To))
         elsif Get_Type_Kind (To) = EW_Builtin
         then EW_Bool_Type
         else EW_Split (Get_Ada_Node (+To)));
      --  Concrete type for To if To is a wrapper for initialization

      --  Do not generate a predicate check for an internal call to a parent
      --  predicate function inside the definition of a predicate function.
      Do_Predicate_Check : constant Boolean :=
        Present (Ada_Node)
          and then not No_Init
          and then Present (Get_Ada_Node (+To))
          and then Has_Predicates (Get_Ada_Node (+To))
          and then Get_Ada_Node (+To) /= Get_Ada_Node (+From)
          and then not Skip_Pred
          and then not Is_Call_Arg_To_Predicate_Function (Ada_Node);

      --  Current result expression
      Result : W_Expr_Id := Expr;

      --  Current type of the result expression
      Cur : W_Type_Id := From;

      --  Set to True after range check has been applied
      Range_Check_Applied : Boolean := False;

   --  Start of processing for Insert_Scalar_Conversion

   begin
      --  If the check is a range check on a floating-point type, and we can
      --  determine that the expression is always within bounds, then issue
      --  a check always true. Do not apply this optimization to actual
      --  parameters of calls, as Determine_Range_R does not work for out and
      --  in out parameters, as it will return the range of the actual based
      --  on its type rather than based on the type of the formal parameter.
      --  For the same reason, do not apply also this optimization on lvalues.

      if Present (Range_Type)
        and then Is_Floating_Point_Type (Range_Type)
        and then not
          (Is_Converted_Actual_Output_Parameter (Ada_Node) or else Lvalue)
      then
         declare
            Tlo : constant Node_Id := Type_Low_Bound  (Range_Type);
            Thi : constant Node_Id := Type_High_Bound (Range_Type);
            Lov : Ureal;
            Hiv : Ureal;
            Lo  : Ureal := No_Ureal;
            Hi  : Ureal := No_Ureal;
            OK  : Boolean;

         begin
            --  The computation of the range assumes at worst that the type of
            --  the expression is respected, so it is not suitable for overflow
            --  checks, for example the overflow check on 'Pred and 'Succ,
            --  therefore test first that Check_Kind is a range check.

            if Check_Kind = RCK_Range

              --  We can only remove the check if we can compute the expected
              --  bounds of the Range_Type now.

              and then Compile_Time_Known_Value (Tlo)
              and then Compile_Time_Known_Value (Thi)
            then
               Lov := Expr_Value_R (Tlo);
               Hiv := Expr_Value_R (Thi);

               --  Call Determine_Range_R on floating-point values

               if Is_Floating_Point_Type (Etype (Ada_Node)) then
                  Determine_Range_R (Ada_Node, OK, Lo, Hi,
                                     Assume_Valid => True);

               --  Call Determine_Range on integer values, which may happen
               --  when converting an integer to a floating-point type.

               elsif Is_Discrete_Type (Etype (Ada_Node)) then
                  declare
                     use Eval_Fat;

                     function Round_Machine (B : Ureal) return Ureal is
                       (Machine (Range_Type, B, Round_Even, Ada_Node));
                     --  This is similar to the homonym function in
                     --  Checks.Determine_Range_R. It rounds a real bound B
                     --  using mode Round_Even. The underlying floating-point
                     --  type used is Range_Type.

                     Lo_Int, Hi_Int : Uint;
                  begin
                     Determine_Range (Ada_Node, OK, Lo_Int, Hi_Int,
                                      Assume_Valid => True);

                     if OK then
                        Lo := Round_Machine (UR_From_Uint (Lo_Int));
                        Hi := Round_Machine (UR_From_Uint (Hi_Int));
                     end if;
                  end;

               --  Neither a floating-point nor an integer value, hence
               --  fixed-point value. This case is not optimized for now.

               else
                  OK := False;
               end if;

               if OK then

                  --  If definitely in range, generate a check always true for
                  --  the range check. When gnat2why directly handles check
                  --  messages, a message could be generated instead here.

                  if Lo >= Lov and then Hi <= Hiv then
                     Emit_Always_True_Range_Check (Ada_Node, Check_Kind);
                     Range_Check_Applied := True;
                  end if;
               end if;
            end if;
         end;
      end if;

      --  The regular case, we take care to insert the range check at a
      --  valid place where the expression is of the appropriate Why base
      --  type (real for a range check of a floating point type, bitvector_?
      --  for a range check of a modular type, int for a range check of a
      --  discrete type).

      --  0. If From is a wrapper type, access the value. This may introduce an
      --     initialization check.

      if Is_Init_Wrapper_Type (From) then
         declare
            From_Node : constant Entity_Id := Get_Ada_Node (+From);
         begin
            if Domain = EW_Prog and then not No_Init then
               Result := Insert_Initialization_Check
                 (Ada_Node               => Ada_Node,
                  E                      => From_Node,
                  Name                   => Result,
                  Domain                 => Domain,
                  Exclude_Always_Relaxed => True);
            end if;

            if Get_Type_Kind (From) = EW_Split then
               Result := New_Label (Labels => Symbol_Sets.Empty_Set,
                                    Def    => Result,
                                    Domain => Domain,
                                    Typ    => EW_Split (From_Node));
            elsif From = M_Boolean_Init_Wrapper.Wrapper_Ty then
               Result := New_Call
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Name     => M_Boolean_Init_Wrapper.Of_Wrapper,
                  Args     => (1 => Result),
                  Typ      => EW_Bool_Type);
            else
               Result := New_Call
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Name     => E_Symb (From_Node, WNE_Of_Wrapper),
                  Args     => (1 => Result),
                  Typ      => EW_Abstract (From_Node));
            end if;
         end;
         Cur := Get_Type (Result);
      end if;

      --  1. If From is an abstract type, convert it to type int, __fixed,
      --     real, or bitvector_?.

      if Get_Type_Kind (Cur) = EW_Abstract then
         Cur := Base_Why_Type (From);
         Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                             Domain   => Domain,
                                             To       => Cur,
                                             Expr     => Result);
      end if;

      --  2. If From is a fixed-point type or a modular type, and To does not
      --     share the same base type (__fixed or bitvector_?), possibly
      --     convert to a suitable intermediate type.

      if Base_Why_Type (From) /= Base_Why_Type (To) then

         --  2.1. Possibly convert from one fixed-point small to another one

         if Why_Type_Is_Fixed (Base_Why_Type (From))
           and then Why_Type_Is_Fixed (Base_Why_Type (To))
         then
            declare
               From_Type : constant Entity_Id := Get_Ada_Node (+From);
               To_Type   : constant Entity_Id := Get_Ada_Node (+To);
               To_Base   : constant W_Type_Id := Base_Why_Type (To);

               --  Fixed point types always have an Ada node

               pragma Assert
                 (Present (From_Type)
                  and then Has_Fixed_Point_Type (From_Type)
                  and then Present (To_Type)
                  and then Has_Fixed_Point_Type (To_Type));

               --  If From and To have the same small, they should have the
               --  same base type.

               pragma Assert
                 (Small_Value (From_Type) /= Small_Value (To_Type));

               --  Multiply by 1 to introduce the conversion

               Module   : constant M_Fixed_Point_Mult_Div_Type :=
                 Get_Fixed_Point_Mult_Div_Theory
                   (Typ_Left   => From_Type,
                    Typ_Right  => Standard_Integer,
                    Typ_Result => To_Type);
               Name     : constant W_Identifier_Id := Module.Mult;
               One_Term : constant W_Expr_Id :=
                 New_Discrete_Constant (Value => Uint_1,
                                        Typ   => EW_Int_Type);
            begin
               Result := New_Call (Ada_Node => Ada_Node,
                                   Domain   => Domain,
                                   Name     => Name,
                                   Args     => (1 => Result,
                                                2 => One_Term),
                                   Typ      => To_Base);

               Cur := To_Base;
            end;

         --  2.2. If From is a fixed-point type and To is an integer type,

         elsif (Why_Type_Is_Fixed (Base_Why_Type (From))
                and then not Why_Type_Is_Float (Base_Why_Type (To)))

         --       or if From is a modular type and To is neither a modular nor
         --       a float, insert a conversion to int since we only support
         --       direct conversion from bitvector to int, float or another
         --       bitvector types.

           or else (Why_Type_Is_BitVector (Base_Why_Type (From))
                    and then not Why_Type_Is_BitVector (Base_Why_Type (To))
                    and then not Why_Type_Is_Float (Base_Why_Type (To)))
         then
            Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                                Domain   => Domain,
                                                To       => EW_Int_Type,
                                                Expr     => Result);
            Cur := EW_Int_Type;
         end if;
      end if;

      --  3. Possibly perform the range check, if applicable on Cur. A special
      --     case is that range checks on boolean variables are performed after
      --     their conversion to int. Another special case is that range checks
      --     on modular types are always performed at this point, as any
      --     necessary conversion to int has already occurred in 2.

      if Present (Range_Type)
        and then not Range_Check_Applied
        and then From /= EW_Bool_Type
        and then (Base_Why_Type (Range_Type) = Cur
                   or else
                  Has_Modular_Integer_Type (Range_Type))
      then
         Range_Check_Applied := True;
         Result := +Do_Range_Check (Ada_Node   => Ada_Node,
                                    Ty         => Range_Type,
                                    W_Expr     => Result,
                                    Check_Kind => Check_Kind);
      end if;

      --  4. If From and To do not share the same base type (bool, int, __fixed
      --     bitvector_? or real), convert from one to the other.
      --     Note that for checks, the base type of Boolean is "int".

      if Cur /= Base_Why_Type_No_Bool (To) then
         Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                             Domain   => Domain,
                                             From     => Cur,
                                             To       =>
                                               Base_Why_Type_No_Bool (To),
                                             Expr     => Result);
         Cur := Base_Why_Type_No_Bool (To);
      end if;

      --  5. Possibly perform the range check, if not already applied

      if Present (Range_Type)
        and then not Range_Check_Applied
      then
         pragma Assert (Base_Why_Type (Range_Type) = Cur
                        or else Base_Why_Type (Range_Type) = EW_Bool_Type
                        or else (Get_Type_Kind (Cur) = EW_Split
                          and then Base_Why_Type (Get_Ada_Node (+Cur)) =
                            Base_Why_Type (Range_Type)));
         Result := +Do_Range_Check (Ada_Node   => Ada_Node,
                                    Ty         => Range_Type,
                                    W_Expr     => Result,
                                    Check_Kind => Check_Kind);
      end if;

      --  6. Perform a predicate check if needed, before the final conversion
      --  to the target abstract type if any, if the predicate function takes
      --  a Why3 native type as input as detected by Use_Split_Form_For_Type.

      if Domain = EW_Prog
        and then Do_Predicate_Check
        and then Use_Split_Form_For_Type (Get_Ada_Node (+To))
      then
         Result := +Insert_Predicate_Check (Ada_Node => Ada_Node,
                                            Check_Ty => Get_Ada_Node (+To),
                                            W_Expr   => +Result);
      end if;

      --  7. If To is an abstract type or bool, convert from int, __fixed or
      --     real to it.

      if Get_Type_Kind (To_Conc) = EW_Abstract
        or else To_Conc = EW_Bool_Type
      then
         Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                             Domain   => Domain,
                                             From     => Cur,
                                             To       => To_Conc,
                                             Expr     => Result);

      --  If the type is in split form, no conversion is needed. Change the
      --  Ada_Node to the expected type. We do that by adding a dummy node.

      elsif Get_Type_Kind (To_Conc) = EW_Split then
         Result := New_Label (Labels => Symbol_Sets.Empty_Set,
                              Def    => Result,
                              Domain => Domain,
                              Typ    => To_Conc);
      end if;

      --  8. Perform a predicate check if needed, after the final conversion
      --  to the target abstract type if any, if the predicate function takes
      --  an abstract type as input as detected by Use_Split_Form_For_Type.

      if Domain = EW_Prog
        and then Do_Predicate_Check
        and then not Use_Split_Form_For_Type (Get_Ada_Node (+To))
      then
         Result := +Insert_Predicate_Check (Ada_Node => Ada_Node,
                                            Check_Ty => Get_Ada_Node (+To),
                                            W_Expr   => +Result);
      end if;

      --  9. Reconstruct the wrapper if necessary

      if Is_Init_Wrapper_Type (To) then
         if Get_Type_Kind (To) = EW_Split then
            Result := New_Label (Labels => Symbol_Sets.Empty_Set,
                                 Def    => Result,
                                 Domain => Domain,
                                 Typ    => To);
         elsif To = M_Boolean_Init_Wrapper.Wrapper_Ty then
            Result := New_Call
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Name     => M_Boolean_Init_Wrapper.To_Wrapper,
               Args     => (1 => Result),
               Typ      => To);
         else
            Result := New_Call
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Name     => E_Symb (Get_Ada_Node (+To), WNE_To_Wrapper),
               Args     => (1 => Result),
               Typ      => To);
         end if;
      end if;

      return Result;
   end Insert_Scalar_Conversion;

   ------------------------------
   -- Insert_Simple_Conversion --
   ------------------------------

   function Insert_Simple_Conversion
     (Ada_Node       : Node_Id := Empty;
      Domain         : EW_Domain;
      Expr           : W_Expr_Id;
      To             : W_Type_Id;
      Force_No_Slide : Boolean := False)
      return W_Expr_Id
   is
      From : constant W_Type_Id := Get_Type (Expr);

   begin

      --  Nothing to do if From = To

      if Eq_Base (To, From) then
         return Expr;
      end if;

      if Is_Private_Conversion (To, From)
        or else Is_Record_Conversion (To, From)
      then
         return Insert_Record_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          Expr     => Expr,
                                          To       => To);

      elsif Is_Array_Conversion (To, From) then
         return Insert_Array_Conversion (Domain         => Domain,
                                         Ada_Node       => Ada_Node,
                                         Expr           => Expr,
                                         To             => To,
                                         Force_No_Slide => Force_No_Slide);

      elsif Is_Subp_Pointer_Conversion (From, To) then
         return Insert_Subp_Pointer_Conversion (Domain   => Domain,
                                                Ada_Node => Ada_Node,
                                                Expr     => Expr,
                                                To       => To);

      elsif Is_Pointer_Conversion (To, From) then
         return Insert_Pointer_Conversion (Domain   => Domain,
                                           Ada_Node => Ada_Node,
                                           Expr     => Expr,
                                           To       => To);

      else
         return Insert_Scalar_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          Expr     => Expr,
                                          To       => To,
                                          No_Init  => True);
      end if;
   end Insert_Simple_Conversion;

   ------------------------------
   -- Insert_Single_Conversion --
   ------------------------------

   function Insert_Single_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      To       : W_Type_Id;
      Expr     : W_Expr_Id)
      return W_Expr_Id
   is
      From : constant W_Type_Id := Get_Type (Expr);
   begin
      return Insert_Single_Conversion (Ada_Node => Ada_Node,
                                       Domain   => Domain,
                                       From     => From,
                                       To       => To,
                                       Expr     => Expr);
   end Insert_Single_Conversion;

   function Insert_Single_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      From     : W_Type_Id;
      To       : W_Type_Id;
      Expr     : W_Expr_Id) return W_Expr_Id is
      From_Base : constant W_Type_Id :=
        (if Get_Type_Kind (From) = EW_Split
         and then Has_Scalar_Type (Get_Ada_Node (+From))
         then Base_Why_Type (Get_Ada_Node (+From))
         else From);
      To_Base   : constant W_Type_Id :=
        (if Get_Type_Kind (To) = EW_Split
         and then Has_Scalar_Type (Get_Ada_Node (+To))
         then Base_Why_Type (Get_Ada_Node (+To))
         else To);
   begin
      if Eq_Base (From_Base, To_Base) then
         return Expr;
      end if;

      --  Conversion of integer constants to Why range types are replaced by
      --  builtin range values.

      declare
         Current : W_Expr_Id := Expr;
      begin
         while Get_Kind (+Current) = W_Label loop
            Current := Get_Def (W_Label_Id (Current));
         end loop;

         if Get_Kind (+Current) = W_Integer_Constant
           and then Get_Type_Kind (To) = EW_Abstract
           and then Is_Range_Type_In_Why (Get_Ada_Node (+To))
         then
            return New_Range_Constant
              (Ada_Node => Get_Ada_Node (+Expr),
               Value    => Get_Value (W_Integer_Constant_Id (Current)),
               Typ      => To);
         end if;
      end;

      return
        New_Call (Domain   => Domain,
                  Ada_Node => Ada_Node,
                  Name     => Conversion_Name
                    (From => From_Base, To => To_Base),
                  Args     => (1 => +Expr),
                  Typ      => To);
   end Insert_Single_Conversion;

   ------------------------------------
   -- Insert_Subp_Pointer_Conversion --
   ------------------------------------

   function Insert_Subp_Pointer_Conversion
     (Ada_Node   : Node_Id;
      Domain     : EW_Domain;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False;
      No_Init    : Boolean := False)
      return W_Expr_Id
   is
      From   : constant W_Type_Id := Get_Type (Expr);
      --  Current result expression
      Result : W_Expr_Id := Expr;

      L : constant Node_Id := Get_Ada_Node (+From);
      R : constant Node_Id := Get_Ada_Node (+To);

      Need_Conv           : constant Boolean := not Eq_Base (From, To);

      Need_LSP_Checks     : constant Boolean :=
        Directly_Designated_Type (L) /= Directly_Designated_Type (R);

      Need_Not_Null_Check : constant Boolean := Can_Never_Be_Null (R);

      --  Do not generate a predicate check for an internal call to a parent
      --  predicate function inside the definition of a predicate function.

      Need_Pred_Check     : constant Boolean :=
        not No_Init and then Has_Predicates (R)
        and then not Is_Call_Arg_To_Predicate_Function (Ada_Node);

   begin
      --  When neither checks nor conversions need to be inserted, return

      if not Need_Check and then not Need_Conv then
         return Expr;
      end if;

      --  LSP checks are done before the conversion

      if Need_Check and then Need_LSP_Checks and then Domain = EW_Prog then
         declare
            E_Tmp : constant W_Expr_Id := New_Temp_For_Expr (Expr);
         begin
            Result := +Sequence
              (Ada_Node => Ada_Node,
               Left     => Checks_For_Subp_Conversion
                 (Ada_Node => Ada_Node,
                  Expr     => E_Tmp,
                  From     => L,
                  To       => R,
                  Params   => Body_Params),
               Right    => +E_Tmp);
            Result := Binding_For_Temp
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Tmp      => E_Tmp,
               Context  => Result);
         end;
      end if;

      --  No real conversions are needed, we only need to change the type of
      --  the expression for gnat2why. We use an empty label for that.

      if Need_Conv then
         Result := New_Label
           (Ada_Node => Ada_Node,
            Domain   => Domain,
            Labels   => Symbol_Sets.Empty_Set,
            Def      => Result,
            Typ      => To);
      end if;

      --  Predicate checks and null exclusion checks are performed after the
      --  conversion.

      if Need_Check and then Domain = EW_Prog then

         if Need_Pred_Check then
            Result := +Insert_Predicate_Check (Ada_Node,
                                               R,
                                               +Result);
         end if;

         if Need_Not_Null_Check then
            Result :=
              +New_VC_Call
              (Ada_Node => Ada_Node,
               Name     => To_Program_Space
                 (E_Symb (R, WNE_Assign_Null_Check)),
               Progs    => (1 => +Result),
               Reason   => VC_Null_Exclusion,
               Typ      => Get_Type (Result));
         end if;
      end if;

      return Result;
   end Insert_Subp_Pointer_Conversion;

   -------------
   -- Is_Void --
   -------------

   function Is_Void (W : W_Prog_Id) return Boolean is
   begin
      return W = +Void
             or else
               (Get_Kind (+W) = W_Statement_Sequence
                and then
                Is_Void_List
                  (Statement_Sequence_Get_Statements (+W)));
   end Is_Void;

   ------------------
   -- Is_Void_List --
   ------------------

   function Is_Void_List (L : Why_Node_List) return Boolean is
   begin
      return (for all Node of Get_List (L) => Is_Void (+Node));
   end Is_Void_List;

   -------------------------
   -- Is_Essentially_Void --
   -------------------------

   function Is_Essentially_Void (W : W_Prog_Id) return Boolean is
   begin
      return W = +Void
             or else
               (Get_Kind (+W) = W_Label
                and then
                Is_Essentially_Void (+Label_Get_Def (+W)))
             or else
               (Get_Kind (+W) = W_Loc_Label
                and then
                Is_Essentially_Void (+Loc_Label_Get_Def (+W)))
             or else
               (Get_Kind (+W) = W_Statement_Sequence
                and then
                Is_Essentially_Void_List
                  (Statement_Sequence_Get_Statements (+W)));
   end Is_Essentially_Void;

   ------------------------------
   -- Is_Essentially_Void_List --
   ------------------------------

   function Is_Essentially_Void_List (L : Why_Node_List) return Boolean is
   begin
      return (for all Node of Get_List (L) => Is_Essentially_Void (+Node));
   end Is_Essentially_Void_List;

   ----------------------
   -- Is_False_Boolean --
   ----------------------

   function Is_False_Boolean (P : W_Expr_Id) return Boolean is
   begin
      return
         Get_Kind (+P) = W_Literal and then
         Get_Value (+P) = EW_False;
   end Is_False_Boolean;

   ---------------------
   -- Is_True_Boolean --
   ---------------------

   function Is_True_Boolean (P : W_Expr_Id) return Boolean is
   begin
      return
         Get_Kind (+P) = W_Literal and then
         Get_Value (+P) = EW_True;
   end Is_True_Boolean;

   -----------------
   -- Needs_Slide --
   -----------------

   function Needs_Slide (From_Ent, To_Ent : Entity_Id) return Boolean is

      function First_Constrained_Parent (Ty : Entity_Id) return Entity_Id with
        Pre => Is_Constrained (Ty);
      --  Traverse the parents of Ty to find the first constrained type

      ------------------------------
      -- First_Constrained_Parent --
      ------------------------------

      function First_Constrained_Parent (Ty : Entity_Id) return Entity_Id is
         Parent : Entity_Id := Retysp (Ty);
      begin
         loop
            declare
               New_Parent : constant Entity_Id := Parent_Retysp (Parent);
            begin
               if No (New_Parent)
                 or else not Is_Constrained (New_Parent)
               then
                  return Parent;
               else
                  Parent := New_Parent;
               end if;
            end;
         end loop;
      end First_Constrained_Parent;

      Dim              : constant Positive :=
        Positive (Number_Dimensions (To_Ent));
      To_Constrained   : constant Boolean := Is_Constrained (To_Ent);
      From_Constrained : constant Boolean := Is_Constrained (From_Ent);
   begin
      --  Sliding is needed when we convert to a constrained type and the
      --  'First of the From type is not known to be equal to the 'First
      --  of the "To" type.

      --  Sliding is only necessary when converting to a constrained array or
      --  to a type with fixed lower bounds.

      if not To_Constrained
        and then not Is_Fixed_Lower_Bound_Array_Subtype (To_Ent)
      then
         return False;
      end if;

      --  When the "To" is constrained, sliding is always necessary when
      --  converting from an unconstrained array without fixed lower bounds

      if not From_Constrained
        and then not Is_Fixed_Lower_Bound_Array_Subtype (From_Ent)
      then
         return True;
      end if;

      --  If "To" and "From" are derived from the same constrained type, no
      --  sliding is needed.

      if From_Constrained
        and then To_Constrained
        and then First_Constrained_Parent (From_Ent) =
        First_Constrained_Parent (To_Ent)
      then
         return False;
      end if;

      --  Go over the indexes to see if one of them needs sliding

      for I in 1 .. Dim loop
         declare
            Typ_From : constant Entity_Id := Nth_Index_Type (From_Ent, I);
            Typ_To   : constant Entity_Id := Nth_Index_Type (To_Ent, I);
            Low_From : Node_Id;
            Low_To   : Node_Id;

         begin
            --  If To has no constraints for this index, we don't need sliding
            --  for the current dimension.

            if not To_Constrained
              and then not Is_Fixed_Lower_Bound_Index_Subtype (Typ_To)
            then
               null;

            --  If From has no constraints for this index, sliding is needed

            elsif not From_Constrained
              and then not Is_Fixed_Lower_Bound_Index_Subtype (Typ_From)
            then
               return True;

            --  Both lower bounds are constrained, check that they have the
            --  same value.

            else
               Low_From := Type_Low_Bound (Retysp (Typ_From));
               Low_To := Type_Low_Bound (Retysp (Typ_To));

               if not Is_Static_Expression (Low_From)
                 or else not Is_Static_Expression (Low_To)
                 or else Expr_Value (Low_From) /= Expr_Value (Low_To)
               then
                  return True;
               end if;
            end if;
         end;
      end loop;

      --  We statically know that the "first" are actually equal, no sliding
      --  needed

      return False;
   end Needs_Slide;

   ----------------------
   -- New_Ada_Equality --
   ----------------------

   function New_Ada_Equality
     (Typ         : Type_Kind_Id;
      Domain      : EW_Domain;
      Left, Right : W_Expr_Id)
      return W_Expr_Id
   is
      Why_Type   : constant W_Type_Id := Type_Of_Node (Typ);
      Use_Predef : constant Boolean :=
        Use_Predefined_Equality_For_Type (Typ);
      Eq_Id      : constant W_Identifier_Id :=
        (if Is_Boolean_Type (Typ) then M_Boolean.Bool_Eq
         elsif Use_Predef then E_Symb (Typ, WNE_Bool_Eq)
         else E_Symb (Typ, WNE_User_Eq));
      T          : W_Expr_Id;

   begin
      if Is_Class_Wide_Type (Typ) then
         --  Dispatching equality. Translate to:
         --  let a = to_root left in
         --  let b = to_root right in
         --    a.attr_tag = b.attr_tag /\
         --    __dispatch_eq a b

         declare
            Subdomain : constant EW_Domain :=
              (if Domain = EW_Pred then EW_Term else Domain);
            Root      : constant Entity_Id := Root_Retysp (Typ);
            Args      : constant W_Expr_Array :=
              (1 => New_Temp_For_Expr
                 (Insert_Simple_Conversion
                      (Domain => Subdomain,
                       Expr   => Left,
                       To     => Type_Of_Node (Root))),
               2 => New_Temp_For_Expr
                 (Insert_Simple_Conversion
                      (Domain => Subdomain,
                       Expr   => Right,
                       To     => Type_Of_Node (Root))));
         begin
            T := New_And_Then_Expr
              (Left   => New_Call
                 (Domain => Domain,
                  Name   => Why_Eq,
                  Args   =>
                    (1 => New_Tag_Access
                         (Domain => Subdomain,
                          Name   => Args (1),
                          Ty     => Root),
                     2 => New_Tag_Access
                       (Domain => Subdomain,
                        Name   => Args (2),
                        Ty     => Root)),
                  Typ    => EW_Bool_Type),
               Right  =>
                 New_Call
                   (Domain => Domain,
                    Name   =>
                      E_Symb (Root, WNE_Dispatch_Eq),
                    Args   => New_Tag_Access
                      (Domain => Subdomain,
                       Name   => Args (1),
                       Ty     => Root)
                    & Args,
                    Typ    => EW_Bool_Type),
               Domain => Domain);

            T := Binding_For_Temp (Domain  => Domain,
                                   Tmp     => Args (1),
                                   Context => T);
            T := Binding_For_Temp (Domain  => Domain,
                                   Tmp     => Args (2),
                                   Context => T);
         end;
      elsif Is_Scalar_Type (Typ) then
         declare
            BT       : constant W_Type_Id := Base_Why_Type_No_Bool (Why_Type);
            Left_Int : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain => EW_Term,
                 Expr => Left,
                 To   => BT);
            Right_Int : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain => EW_Term,
                 Expr => Right,
                 To   => BT);

         begin
            if Use_Predef then
               if Why_Type_Is_Float (BT) then
                  T :=
                    New_Call
                      (Name   => MF_Floats (BT).Eq,
                       Domain => Domain,
                       Typ    => EW_Bool_Type,
                       Args   => (Left_Int, Right_Int));
               elsif Why_Type_Is_BitVector (BT) then
                  T :=
                    New_Call
                      (Name   => (if Domain in EW_Prog | EW_Pterm then
                                    MF_BVs (BT).Prog_Eq
                                  else Why_Eq),
                       Domain => Domain,
                       Typ    => EW_Bool_Type,
                       Args   => (Left_Int, Right_Int));
               else
                  T :=
                    New_Call
                      (Name   => Why_Eq,
                       Domain => Domain,
                       Typ    => EW_Bool_Type,
                       Args   => (Left_Int, Right_Int));
               end if;

            else
               T :=
                 New_Call
                   (Name   => Eq_Id,
                    Domain => EW_Term,
                    Args   => (1 => Left_Int, 2 => Right_Int),
                    Typ   => EW_Bool_Type);
            end if;
         end;
      else
         T :=
           New_Call
             (Name   => Eq_Id,
              Domain => EW_Term,
              Args   =>
                (1 => Left,
                 2 => Right),
              Typ   => EW_Bool_Type);
      end if;

      return T;
   end New_Ada_Equality;

   ------------------
   -- New_And_Expr --
   ------------------

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain)
       return W_Expr_Id is
   begin
      if Is_True_Boolean (+Left) then
         return Right;
      elsif Is_True_Boolean (+Right) then
         return Left;
      elsif Domain = EW_Pred then
         return New_Connection (Domain => Domain,
                                Op     => EW_And,
                                Left   => +Left,
                                Right  => +Right);
      else
         return New_Call (Domain => Domain,
                          Name   => M_Boolean.Andb,
                          Args   => (1 => +Left, 2 => +Right),
                          Typ    => EW_Bool_Type);
      end if;
   end New_And_Expr;

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain;
       Base        : W_Type_Id) return W_Expr_Id is
   begin
      if Base = EW_BitVector_8_Type or else
        Base = EW_BitVector_16_Type or else
        Base = EW_BitVector_32_Type or else
        Base = EW_BitVector_64_Type or else
        Base = EW_BitVector_128_Type
      then
         return
           New_Call (Domain => Domain,
                     Name   => MF_BVs (Base).BW_And,
                     Args   => (1 => +Left, 2 => +Right),
                     Typ    => Base);
      elsif Base = EW_Bool_Type then
         return New_And_Expr (Left, Right, Domain);
      else
         declare
            Left2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Left,
                                            To     => EW_Bool_Type)
               else Left);
            Right2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Right,
                                            To     => EW_Bool_Type)
               else Right);
         begin
            return New_And_Expr (Left2, Right2, Domain);
         end;
      end if;
   end New_And_Expr;

   ------------------
   -- New_And_Pred --
   ------------------

   function New_And_Pred (Conjuncts : W_Pred_Array) return W_Pred_Id is
   begin
      if Conjuncts'Length = 0 then
         return False_Pred;

      elsif Conjuncts'Length = 1 then
         return Conjuncts (Conjuncts'First);

      else
         declare
            More : constant W_Expr_Array :=
              (for J in Conjuncts'First + 2 .. Conjuncts'Last =>
                 +Conjuncts (J));
         begin
            return New_Connection
              (Op         => EW_And,
               Left       => Conjuncts (Conjuncts'First),
               Right      => Conjuncts (Conjuncts'First + 1),
               More_Right => More);
         end;
      end if;
   end New_And_Pred;

   -----------------------
   -- New_And_Then_Expr --
   -----------------------

   function New_And_Then_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain)
       return W_Expr_Id
   is
   begin
      if Is_True_Boolean (+Left) then
         return Right;
      elsif Is_True_Boolean (+Right) then
         return Left;
      else
         if Domain = EW_Prog then
            return
               New_Connection
                 (Op     => EW_And_Then,
                  Left   => Left,
                  Right  => Right,
                  Domain => Domain);
         else
            return New_And_Expr (Left, Right, Domain);
         end if;
      end if;
   end New_And_Then_Expr;

   ------------------------
   -- New_Attribute_Expr --
   ------------------------

   function New_Attribute_Expr
     (Ty        : Entity_Id;
      Domain    : EW_Domain;
      Attr      : Supported_Attribute_Id;
      Params    : Transformation_Params := Body_Params)
      return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
        (if Domain in EW_Prog | EW_Pterm then EW_Pterm else EW_Term);

   begin
      --  We do not generate axioms giving values to bounds of Itypes as they
      --  may contain locally defined entities that are not detected by
      --  Get_Variables ('Old, 'Loop_Entry, 'Return).

      if Attr in Attribute_First | Attribute_Last
        and then Type_Is_Modeled_As_Base (Ty)
        and then Is_Itype (Ty)
      then
         --  Use expression for dynamic bounds

         declare
            Rng : constant Node_Id := Get_Range (Ty);
            BT  : constant W_Type_Id :=
              (if Is_Standard_Boolean_Type (Ty) then EW_Int_Type
               else Base_Why_Type (Ty));
         begin
            return Transform_Expr ((if Attr = Attribute_First
                                    then Low_Bound (Rng)
                                    else High_Bound (Rng)),
                                   BT, Subdomain, Params);
         end;

      elsif Attr in Attribute_First | Attribute_Last
        and then Type_Is_Modeled_As_Base (Ty)
      then
         --  Call predefind functions

         declare
            Rng : constant Node_Id := Get_Range (Ty);
            BT  : constant W_Type_Id :=
              (if Is_Standard_Boolean_Type (Ty) then EW_Int_Type
               else Base_Why_Type (Ty));
            Bnd : constant Node_Id :=
              (if Attr = Attribute_First then Low_Bound (Rng)
               else High_Bound (Rng));
            Id  : constant W_Identifier_Id :=
              (if Attr = Attribute_First then E_Symb (Ty, WNE_Attr_First)
               else E_Symb (Ty, WNE_Attr_Last));
         begin
            return New_Call (Domain   => Subdomain,
                             Name     => Id,
                             Args     => Get_Args_From_Binders
                               (To_Binder_Array
                                  (Get_Binders_From_Expression (Bnd),
                                   Keep_Const => Keep),
                                Params.Ref_Allowed),
                             Typ      => BT);
         end;

      elsif Attr in Attribute_First | Attribute_Last | Attribute_Length
        and then Ekind (Ty) = E_String_Literal_Subtype
      then
         declare
            BT : constant W_Type_Id := Nth_Index_Rep_Type_No_Bool
              (Ty, 1);
         begin
            case Attr is
            when Attribute_First =>
               return New_Discrete_Constant
                 (Value => Expr_Value (String_Literal_Low_Bound (Ty)),
                  Typ   => BT);

            when Attribute_Length =>
               return New_Integer_Constant
                 (Value => String_Literal_Length (Ty));

            when Attribute_Last =>
               return New_Discrete_Constant
                 (Value => Expr_Value (String_Literal_Low_Bound (Ty)) +
                    String_Literal_Length (Ty) - 1,
                  Typ   => BT);

            when others =>
               raise Program_Error;
            end case;
         end;

      elsif Is_Standard_Boolean_Type (Ty) then
         case Attr is
            when Attribute_First => return +M_Boolean.First;
            when Attribute_Last  => return +M_Boolean.Last;
            when Attribute_Image => return +M_Boolean.Image;
            when Attribute_Value => return +M_Boolean.Value;
            when others =>
               raise Program_Error;
         end case;

      else
         case Attr is
            when Attribute_First       => return +E_Symb (Ty, WNE_Attr_First);
            when Attribute_Last        => return +E_Symb (Ty, WNE_Attr_Last);
            when Attribute_Alignment      =>
               return +E_Symb (Ty, WNE_Attr_Alignment);
            when Attribute_Modulus        =>
               return +E_Symb (Ty, WNE_Attr_Modulus);
            when Attribute_Constrained    =>
               return +E_Symb (Ty, WNE_Attr_Constrained);
            when Attribute_Size           =>
               return +E_Symb (Ty, WNE_Attr_Value_Size);
            when Attribute_Component_Size =>
               return +E_Symb (Ty, WNE_Attr_Component_Size);
            when Attribute_Tag            =>
               return +E_Symb (Ty, WNE_Attr_Tag);
            when Attribute_Image          =>
               return +E_Symb (Ty, WNE_Attr_Image);
            when Attribute_Value          =>
               return +E_Symb (Ty, WNE_Attr_Value);
            when others =>
               raise Program_Error;
         end case;
      end if;
   end New_Attribute_Expr;

   ------------------------
   -- New_Binary_Op_Expr --
   ------------------------

   function New_Binary_Op_Expr
     (Op          : N_Binary_Op;
      Left        : W_Expr_Id;
      Right       : W_Expr_Id;
      Left_Type   : Type_Kind_Id;
      Right_Type  : Type_Kind_Id;
      Return_Type : Type_Kind_Id;
      Domain      : EW_Domain;
      Ada_Node    : Node_Id := Empty)
      return W_Expr_Id
   is
      Left_Rep  : W_Expr_Id := Left;
      Right_Rep : W_Expr_Id := Right;
      Base      : W_Type_Id := Why_Empty;
      T         : W_Expr_Id;

   begin
      case Op is
         when N_Op_Compare
            | N_Op_And
            | N_Op_Or
            | N_Op_Xor
            | N_Op_Concat
            | N_Op_Shift
         =>
            raise Program_Error;

         when N_Op_Add
            | N_Op_Subtract
         =>
            Base := Base_Why_Type (Left_Type, Right_Type);

            declare
               Name : constant W_Identifier_Id :=
                 (if Op = N_Op_Add then
                    (if Base = EW_Int_Type then Int_Infix_Add
                     elsif Why_Type_Is_BitVector (Base) then
                       MF_BVs (Base).Add
                     elsif Why_Type_Is_Fixed (Base) then Fixed_Infix_Add
                     else MF_Floats (Base).Add)
                  else
                    (if Base = EW_Int_Type then Int_Infix_Subtr
                     elsif Why_Type_Is_BitVector (Base) then
                          MF_BVs (Base).Sub
                     elsif Why_Type_Is_Fixed (Base) then Fixed_Infix_Subtr
                     else MF_Floats (Base).Subtr));
            begin
               Left_Rep :=
                 Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                           Domain   => Domain,
                                           Expr     => Left,
                                           To       => Base);
               Right_Rep :=
                 Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                           Domain   => Domain,
                                           Expr     => Right,
                                           To       => Base);

               if Has_Modular_Integer_Type (Return_Type)
                 and then Non_Binary_Modulus (Return_Type)
               then
                  T := Transform_Non_Binary_Modular_Operation
                    (Ada_Node   => Ada_Node,
                     Ada_Type   => Return_Type,
                     Domain     => Domain,
                     Op         => Op,
                     Left_Opnd  => Left_Rep,
                     Right_Opnd => Right_Rep,
                     Rep_Type   => Base,
                     Modulus    => Modulus (Return_Type));

               else
                  T :=
                    New_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => Name,
                       Args     => (1 => Left_Rep,
                                    2 => Right_Rep),
                       Typ   => Base);
                  T := Apply_Modulus (Op, Return_Type, T, Domain);
               end if;
            end;

         when N_Op_Multiply =>
            declare
               L_Type, R_Type : W_Type_Id;
               Oper           : Why_Name_Enum := WNE_Empty;

            begin
               --  Look for the appropriate base scalar type

               if Has_Fixed_Point_Type (Left_Type)
                 and then Has_Fixed_Point_Type (Right_Type)
               then
                  L_Type := Base_Why_Type (Left_Type);
                  R_Type := Base_Why_Type (Right_Type);
                  Oper := WNE_Fixed_Point_Mult;

                  if Has_Fixed_Point_Type (Return_Type) then
                     Base := Base_Why_Type (Return_Type);
                  else
                     pragma Assert (Has_Integer_Type (Return_Type));
                     Base := EW_Int_Type;
                  end if;

               elsif Has_Fixed_Point_Type (Left_Type) then
                  L_Type := Base_Why_Type (Left_Type);
                  R_Type := EW_Int_Type;
                  Base := Base_Why_Type (Return_Type);
                  Oper := WNE_Fixed_Point_Mult_Int;
                  pragma Assert (L_Type = Base);

               --  If multiplying an integer and a fixed-point, swap
               --  arguments so that Left is the fixed-point one.

               elsif Has_Fixed_Point_Type (Right_Type) then
                  L_Type    := Base_Why_Type (Right_Type);
                  R_Type    := EW_Int_Type;
                  Left_Rep  := Right;
                  Right_Rep := Left;
                  Base      := Base_Why_Type (Return_Type);
                  Oper      := WNE_Fixed_Point_Mult_Int;
                  pragma Assert (L_Type = Base);

               else
                  Base := Base_Why_Type (Left_Type, Right_Type);
                  L_Type := Base;
                  R_Type := Base;
                  pragma Assert (not Has_Fixed_Point_Type (Return_Type));
               end if;

               Left_Rep := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Left_Rep,
                  To       => L_Type);
               Right_Rep := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Right_Rep,
                  To       => R_Type);

               --  Construct the operation

               if Has_Fixed_Point_Type (Left_Type)
                 or else Has_Fixed_Point_Type (Right_Type)
               then
                  declare
                     pragma Assert (Oper /= WNE_Empty);
                     Name   : W_Identifier_Id;
                  begin
                     case Oper is
                        when WNE_Fixed_Point_Mult =>
                           Name := Get_Fixed_Point_Mult_Div_Theory
                             (Typ_Left   => Left_Type,
                              Typ_Right  => Right_Type,
                              Typ_Result => Return_Type).Mult;

                        when WNE_Fixed_Point_Mult_Int =>
                           Name := Get_Fixed_Point_Theory
                             (Typ => Return_Type).Mult_Int;

                        when others =>
                           raise Program_Error;
                     end case;

                     T := New_Call (Ada_Node => Ada_Node,
                                    Domain   => Domain,
                                    Name     => Name,
                                    Args     => (1 => Left_Rep,
                                                 2 => Right_Rep),
                                    Typ      => Base);
                  end;

               elsif Has_Modular_Integer_Type (Return_Type)
                 and then Non_Binary_Modulus (Return_Type)
               then
                  T := Transform_Non_Binary_Modular_Operation
                    (Ada_Node   => Ada_Node,
                     Ada_Type   => Return_Type,
                     Domain     => Domain,
                     Op         => Op,
                     Left_Opnd  => Left_Rep,
                     Right_Opnd => Right_Rep,
                     Rep_Type   => Base,
                     Modulus    => Modulus (Return_Type));

               else
                  declare
                     Name : constant W_Identifier_Id :=
                       (if Base = EW_Int_Type then Int_Infix_Mult
                        elsif Why_Type_Is_BitVector (Base) then
                          MF_BVs (Base).Mult
                        elsif Why_Type_Is_Fixed (Base) then Fixed_Infix_Mult
                        else MF_Floats (Base).Mult);
                  begin
                     T :=
                       New_Call
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Name     => Name,
                          Args     => (1 => Left_Rep, 2 => Right_Rep),
                          Typ      => Base);
                  end;
                  T := Apply_Modulus (Op, Return_Type, T, Domain);
               end if;

               if Base_Why_Type (Return_Type) /= Base then
                  T := Insert_Checked_Conversion
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Expr     => T,
                     To       => Base_Why_Type (Return_Type));
               end if;
            end;

         when N_Op_Divide =>
            declare
               Oper           : Why_Name_Enum := WNE_Empty;
               Name           : W_Identifier_Id;
               L_Type, R_Type : W_Type_Id;

            begin
               --  Look for the appropriate base scalar type

               if Has_Fixed_Point_Type (Left_Type)
                 and then Has_Fixed_Point_Type (Right_Type)
               then
                  L_Type := Base_Why_Type (Left_Type);
                  R_Type := Base_Why_Type (Right_Type);
                  Oper   := WNE_Fixed_Point_Div;

                  if Has_Fixed_Point_Type (Return_Type) then
                     Base := Base_Why_Type (Return_Type);
                  else
                     pragma Assert (Has_Integer_Type (Return_Type));
                     Base := EW_Int_Type;
                  end if;

               elsif Has_Fixed_Point_Type (Left_Type) then
                  Base   := Base_Why_Type (Return_Type);
                  L_Type := Base_Why_Type (Left_Type);
                  R_Type := EW_Int_Type;
                  Oper   := WNE_Fixed_Point_Div_Int;
                  pragma Assert (L_Type = Base);

               else
                  pragma Assert (not Has_Fixed_Point_Type (Return_Type));
                  Base   := Base_Why_Type (Left_Type, Right_Type);
                  L_Type := Base;
                  R_Type := Base;
               end if;

               pragma Assert
                 (if Has_Fixed_Point_Type (Return_Type)
                    or else Has_Fixed_Point_Type (Left_Type)
                  then Oper /= WNE_Empty);

               --  Construct the operation

               case Oper is
                  when WNE_Fixed_Point_Div =>
                     Name := Get_Fixed_Point_Mult_Div_Theory
                       (Typ_Left   => Left_Type,
                        Typ_Right  => Right_Type,
                        Typ_Result => Return_Type).Div;

                  when WNE_Fixed_Point_Div_Int =>
                     Name := Get_Fixed_Point_Theory
                       (Typ => Return_Type).Div_Int;

                  when others =>
                     Name := New_Division (Base);
               end case;

               Left_Rep := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Left,
                  To       => L_Type);
               Right_Rep := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Right,
                  To       => R_Type);

               T := New_Operator_Call
                 (Ada_Node   => Ada_Node,
                  Domain     => Domain,
                  Name       => Name,
                  Args       => (1 => Left_Rep, 2 => Right_Rep),
                  Reason     => VC_Division_Check,
                  Check_Info => New_Check_Info
                    (Divisor => Get_Ada_Node (+Right)),
                  Check      => (Domain = EW_Prog
                                 and then Present (Ada_Node)
                                 and then Do_Division_Check (Ada_Node)),
                  Typ        => Base);

               if Base_Why_Type (Return_Type) /= Base then
                  T := Insert_Checked_Conversion
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Expr     => T,
                     To       => Base_Why_Type (Return_Type));
               end if;
            end;

         when N_Op_Rem
            | N_Op_Mod
         =>
            declare
               Base : constant W_Type_Id :=
                 Base_Why_Type (Left_Type, Right_Type);
               Name : W_Identifier_Id;

            begin
               Name := (if Why_Type_Is_BitVector (Base) then
                          MF_BVs (Base).Urem
                        elsif Op = N_Op_Rem then
                          M_Int_Div.Rem_Id
                        else M_Int_Div.Mod_Id);

               T := New_Operator_Call
                 (Ada_Node   => Ada_Node,
                  Domain     => Domain,
                  Name       => Name,
                  Args       =>
                    (1 => Insert_Simple_Conversion
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Expr     => Left,
                          To       => Base),
                     2 => Insert_Simple_Conversion
                       (Ada_Node => Ada_Node,
                        Domain   => Domain,
                        Expr     => Right,
                        To       => Base)),
                  Check      => Domain = EW_Prog,
                  Reason     => VC_Division_Check,
                  Check_Info => New_Check_Info
                    (Divisor => Get_Ada_Node (+Right)),
                  Typ        => Base);
            end;

         when N_Op_Expon =>
            declare
               Name  : W_Identifier_Id;
               Typ   : constant W_Type_Id := Base_Why_Type (Left_Type);
               Value : constant W_Expr_Id :=
                 New_Temp_For_Expr
                   (Insert_Simple_Conversion
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Expr     => Left,
                       To       => Typ));
               Expon : constant W_Expr_Id :=
                 New_Temp_For_Expr
                   (Insert_Simple_Conversion
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Expr     => Right,
                       To       => EW_Int_Type));
            begin
               Base := Typ;

               if Has_Modular_Integer_Type (Return_Type)
                 and then Non_Binary_Modulus (Return_Type)
               then
                  T := Transform_Non_Binary_Modular_Operation
                    (Ada_Node   => Ada_Node,
                     Ada_Type   => Return_Type,
                     Domain     => Domain,
                     Op         => Op,
                     Left_Opnd  => Value,
                     Right_Opnd => Expon,
                     Rep_Type   => Typ,
                     Modulus    => Modulus (Return_Type));

               else
                  Name := New_Exp (Typ);

                  T := New_Call
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Name     => Name,
                     Args     => (1 => Value, 2 => Expon),
                     Typ      => Typ);

                  T := Apply_Modulus (Op, Return_Type, T, Domain);

                  --  Exponentiation on floats can actually cause a division
                  --  check, when the base is 0 and the exponent is negative.

                  if Domain = EW_Prog
                    and then Is_Floating_Point_Type (Left_Type)
                  then
                     declare
                        Expon_Negative : constant W_Pred_Id :=
                          New_Comparison
                            (Int_Infix_Lt,
                             +Expon,
                             New_Integer_Constant (Value => Uint_0));
                        Value_Zero     : constant W_Pred_Id :=
                          New_Comparison
                            (Why_Neq,
                             +Value,
                             +MF_Floats (Typ).Plus_Zero);
                        Ass           : constant W_Prog_Id :=
                          New_Located_Assert
                            (Ada_Node   => Ada_Node,
                             Pred       =>
                               New_Simpl_Conditional
                                 (Condition => Expon_Negative,
                                  Then_Part => Value_Zero,
                                  Else_Part => True_Pred),
                             Reason     => VC_Division_Check,
                             Check_Info => New_Check_Info
                               (Divisor => Get_Ada_Node (+Right)),
                             Kind       => EW_Assert);
                     begin
                        Prepend (Ass, T);
                     end;
                  end if;
               end if;

               T := Binding_For_Temp (Ada_Node, Domain, Value, T);
               T := Binding_For_Temp (Ada_Node, Domain, Expon, T);
            end;
      end case;

      if Domain = EW_Prog
        and then Op in N_Op_Add | N_Op_Subtract | N_Op_Multiply | N_Op_Expon
        and then Has_No_Wrap_Around_Annotation (Return_Type)
      then
         declare
            Check : constant W_Prog_Id :=
              Check_No_Wrap_Around_Modular_Operation
                (Ada_Node   => Ada_Node,
                 Ada_Type   => Return_Type,
                 Op         => Op,
                 Left_Opnd  => Left_Rep,
                 Right_Opnd => Right_Rep,
                 Rep_Type   => Base,
                 Modulus    => Modulus (Return_Type));
         begin
            Prepend (Check, T);
         end;
      end if;

      return T;
   end New_Binary_Op_Expr;

   ---------------------
   -- New_Check_Label --
   ---------------------

   function New_Check_Label
     (Sloc : Source_Ptr;
      Reason : VC_Kind;
      Id : VC_Id)
      return Symbol
   is
   begin
      return NID (GP_Check_Marker & Image (Integer (Id), 1) & ":"
                  & VC_Kind'Image (Reason) & ":"
                  & New_Located_String (Sloc));
   end New_Check_Label;

   --------------------
   -- New_Comparison --
   --------------------

   function New_Comparison
     (Symbol      : W_Identifier_Id;
      Left, Right : W_Expr_Id;
      Domain      : EW_Domain)
      return W_Expr_Id
   is
      Operator : W_Identifier_Id := Symbol;
      Left1    : W_Expr_Id;
      Right1   : W_Expr_Id;
      Arg_Type : constant W_Type_Id := Get_Type (Left);
   begin

      --  The only comparisons between Boolean operands that we translate in
      --  Why without going throught integers are the equality and inequality
      --  in a predicate context, translated as equivalence or inequivalence.

      if Arg_Type = EW_Bool_Type
        and then
          ((Symbol /= Why_Eq and then Symbol /= Why_Neq)
           or else Domain /= EW_Pred)
      then
         Left1  :=
           Insert_Simple_Conversion
             (Domain => Domain,
              Expr   => Left,
              To     => EW_Int_Type);
         Right1 :=
           Insert_Simple_Conversion
             (Domain => Domain,
              Expr   => Right,
              To     => EW_Int_Type);
      else
         Left1  := Left;
         Right1 := Right;
      end if;

      --  We enforce float equality, instead of why3 equality,
      --  when comparing floats.
      if Why_Type_Is_Float (Arg_Type) then
         if Symbol = Why_Eq then
            Operator := MF_Floats (Arg_Type).Eq;
         elsif Symbol = Why_Neq then
            Operator := MF_Floats (Arg_Type).Neq;
         end if;
      end if;

      return
        New_Call
          (Domain => Domain,
           Name   => Operator,
           Args   => (Left1, Right1),
           Typ    => EW_Bool_Type);
   end New_Comparison;

   --------------------------
   -- New_Dynamic_Property --
   --------------------------

   function New_Dynamic_Property
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Expr   : W_Term_Id;
      Params : Transformation_Params := Body_Params)
      return W_Expr_Id
   is
   begin
      --  For now, only supports dynamic scalar types, unconstrained array
      --  types and record or private types with discriminants.

      if Is_Scalar_Type (Ty)
        and then (Type_Is_Modeled_As_Base (Ty)
                  or else Use_Split_Form_For_Type (Ty))
      then

         pragma Assert (not Depends_On_Discriminant (Get_Range (Ty)));

         return New_Call (Domain => Domain,
                          Name   => Dynamic_Prop_Name (Ty),
                          Args   =>
                            Args_For_Scalar_Dynamic_Property
                              (Ty, +Expr, Term_Domain (Domain), Params),
                          Typ    => EW_Bool_Type);

      elsif Is_Array_Type (Ty) and then not Is_Static_Array_Type (Ty) then
         declare
            Dim   : constant Positive := Positive (Number_Dimensions (Ty));
            Args  : W_Expr_Array (1 .. 2 * Dim);
         begin
            for Count in 0 .. Dim - 1 loop
               declare
                  F_Expr : constant W_Term_Id :=
                    Get_Array_Attr
                      (Expr => Expr,
                       Attr => Attribute_First,
                       Dim  => Count + 1);
                  L_Expr : constant W_Term_Id :=
                    Get_Array_Attr
                      (Expr => Expr,
                       Attr => Attribute_Last,
                       Dim  => Count + 1);
               begin
                  Args (2 * Count + 1) := +F_Expr;
                  Args (2 * Count + 2) := +L_Expr;
               end;
            end loop;

            return New_Dynamic_Property (Domain, Ty, Args, Params);
         end;

      elsif Count_Discriminants (Ty) > 0 and then Is_Constrained (Ty) then
         declare
            Base_Expr : constant W_Expr_Id :=
              Insert_Simple_Conversion (Domain   => EW_Term,
                                        Ada_Node => Ty,
                                        To       =>
                                          EW_Abstract
                                            (Root_Retysp (Ty)),
                                        Expr     => +Expr);
         begin
            return New_Call
              (Name   => Range_Pred_Name (Root_Retysp (Ty)),
               Args   => Prepare_Args_For_Subtype_Check (Ty, Base_Expr),
               Domain => Domain,
               Typ    => EW_Bool_Type);
         end;

      else
         raise Program_Error;
      end if;
   end New_Dynamic_Property;

   ----------------------
   -- New_Discrete_Add --
   ----------------------

   function New_Discrete_Add
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id;
      Typ    : W_Type_Id := Why_Empty)
      return W_Expr_Id
   is
      Rep_Type : constant W_Type_Id :=
        (if Typ = Why_Empty
         then Base_Why_Type (Get_Type (Left))
         else Base_Why_Type (Typ));
      Op : constant W_Identifier_Id :=
        (if Rep_Type = EW_Int_Type
         then Int_Infix_Add
         else MF_BVs (Rep_Type).Add);
   begin
      pragma Assert (Rep_Type = EW_Int_Type or else
                     Why_Type_Is_BitVector (Rep_Type));

      return
        New_Call
          (Domain => Domain,
           Name   => Op,
           Typ    => Rep_Type,
           Args => (1 =>
                      Insert_Scalar_Conversion
                        (Domain => Domain,
                         Expr   => Left,
                         To     => Rep_Type),
                    2 =>
                      Insert_Scalar_Conversion
                        (Domain => Domain,
                         Expr   => Right,
                         To     => Rep_Type)));
   end New_Discrete_Add;

   ----------------------------
   -- New_Discrete_Substract --
   ----------------------------

   function New_Discrete_Substract
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id;
      Typ    : W_Type_Id := Why_Empty)
      return W_Expr_Id
   is
      Rep_Type : constant W_Type_Id :=
        (if Typ = Why_Empty
         then Base_Why_Type (Get_Type (Left))
         else Base_Why_Type (Typ));
      Op : constant W_Identifier_Id :=
        (if Rep_Type = EW_Int_Type
         then Int_Infix_Subtr
         else MF_BVs (Rep_Type).Sub);
   begin
      pragma Assert (Rep_Type = EW_Int_Type or else
                     Why_Type_Is_BitVector (Rep_Type));

      return
        New_Call
          (Domain => Domain,
           Name   => Op,
           Typ    => Rep_Type,
           Args => (1 =>
                      Insert_Scalar_Conversion
                        (Domain => Domain,
                         Expr   => Left,
                         To     => Rep_Type),
                    2 =>
                      Insert_Scalar_Conversion
                        (Domain => Domain,
                         Expr   => Right,
                         To     => Rep_Type)));
   end New_Discrete_Substract;

   ---------------------------
   -- New_Discrete_Constant --
   ---------------------------

   function New_Discrete_Constant
     (Ada_Node : Node_Id := Empty;
      Value    : Uint;
      Typ      : W_Type_Id)
      return W_Expr_Id
   is
     (if Why_Type_Is_BitVector (Typ)
      then New_Modular_Constant (Ada_Node, Value, Typ)
      else New_Integer_Constant (Ada_Node, Value));

   --------------------
   -- New_Havoc_Call --
   --------------------

   function New_Havoc_Call (Id : W_Identifier_Id) return W_Prog_Id is
      Havoc_Fun : constant W_Identifier_Id :=
        Havoc_Append (Get_Name (Get_Typ (Id)));
   begin
      return New_Call (Name => Havoc_Fun,
                       Args => (1 => +Id));
   end New_Havoc_Call;

   ------------------------
   -- New_Located_String --
   ------------------------

   function New_Located_String (Input : Source_Ptr) return String is
      Slc : Source_Ptr := Input;
      Buf : Unbounded_String;
   begin
      loop
         declare
            File   : constant String := File_Name (Slc);
            Line   : constant Physical_Line_Number :=
              Get_Physical_Line_Number (Slc);
            Column : constant Column_Number := Get_Column_Number (Slc);
         begin
            Append (Buf, File & ':' &
                         Image (Positive (Line), 1) & ':' &
                         Image (Positive (Column), 1));
            exit when Instantiation_Location (Slc) = No_Location;
            Append (Buf, (if Comes_From_Inlined_Body (Slc)
                          then ":inlined:"
                          else ":instantiated:"));
            Slc := Instantiation_Location (Slc);
         end;
      end loop;
      return To_String (Buf);
   end New_Located_String;

   ---------------------
   -- New_Shape_Label --
   ---------------------

   function New_Shape_Label (Node : Node_Id) return Symbol is
      Buf : constant String := Shape_Of_Node (Node);
   begin
      if Buf /= "" then
         return NID (GP_Shape_Marker & Buf);
      else
         return No_Symbol;
      end if;
   end New_Shape_Label;

   -------------------------
   --  New_Comment_Label  --
   -------------------------

   function New_Comment_Label
     (Node   : Node_Id;
      Loc    : Symbol;
      Reason : VC_Kind)
      return Symbol
   is
      Prefix  : constant String := "comment:";
      Str_Loc : constant String := Img (Loc);

      Pointer  : Source_Ptr := Original_Location (Sloc (Node));
      Src_Buff : constant Source_Buffer_Ptr :=
        Source_Text (Get_Source_File_Index (Pointer));

      Buf : Unbounded_String := Null_Unbounded_String;

      Line   : Natural;
      Column : Natural;

      procedure Read_Loc_Label (Line : out Natural; Column : out Natural);

      --------------------
      -- Read_Loc_Label --
      --------------------

      procedure Read_Loc_Label (Line : out Natural; Column : out Natural) is
         Delim_Start : Natural :=
           Ada.Strings.Fixed.Index (Str_Loc, ":",
                                    Ada.Strings.Fixed.Index
                                      (Str_Loc, ":", Str_Loc'First) + 1) + 1;
         Delim_End : Natural;
      begin
         Delim_End := Ada.Strings.Fixed.Index (Str_Loc, ":", Delim_Start);

         Line := Natural'Value (Str_Loc (Delim_Start .. Delim_End - 1));

         Delim_Start := Delim_End + 1;
         Delim_End := Ada.Strings.Fixed.Index (Str_Loc, ":", Delim_Start);
         Delim_End := (if Delim_End /= 0 then Delim_End - 1 else Str_Loc'Last);

         Column := Natural'Value (Str_Loc (Delim_Start .. Delim_End));
      end Read_Loc_Label;

   --  Start of processing for New_Comment_Label

   begin
      Read_Loc_Label (Line, Column);
      Pointer := Line_Start (Physical_Line_Number (Line),
                             Get_Source_File_Index (Pointer));

      while Src_Buff (Pointer) not in ASCII.LF | ASCII.CR
      loop

         Buf := Buf & (if Src_Buff (Pointer) = ASCII.Back_Slash then
                          ASCII.Back_Slash & ASCII.Back_Slash

                       --  Do not print ] in comment as it causes the label to
                       --  end.

                       elsif Src_Buff (Pointer) = ASCII.R_Bracket then ""
                       else Src_Buff (Pointer) & "");
         Pointer := Pointer + 1;
      end loop;

      Buf := Buf & " ";
      Buf := Buf & (1 .. Column - 1 => ' ') & "^ "
        & Str_Loc (9 .. Str_Loc'Last) & ':' & VC_Kind'Image (Reason);
      return NID (Prefix & To_String (Buf));
   end New_Comment_Label;

   -------------------------------
   -- New_Counterexample_Assign --
   -------------------------------

   function New_Counterexample_Assign
     (If_Node   : Node_Id;
      Condition : W_Prog_Id)
      return W_Prog_Id
   is
      Node_Label : constant Symbol_Sets.Set :=
        Symbol_Sets.To_Set
          (NID (Branch_Id_Label &
                Ada.Strings.Fixed.Trim (Source => Node_Id'Image (If_Node),
                                        Side   => Left)));
   begin
      return
        Sequence
          (+Insert_Cnt_Loc_Label
             (Ada_Node => If_Node,
              E        =>
                New_Assignment (Ada_Node => If_Node,
                                Name     => +M_Main.Spark_CE_Branch,
                                Labels   => Node_Label,
                                Value    => Condition,
                                Typ      => EW_Bool_Type)),
           New_Record_Access (Name  =>
                                New_Label
                                  (Ada_Node => If_Node,
                                   Labels   => Node_Label,
                                   Def      => +M_Main.Spark_CE_Branch,
                                   Typ      =>
                                     Get_Typ (M_Main.Spark_CE_Branch)),
                              Field =>
                                +New_Identifier (Name => "bool__content"),
                              Typ   => EW_Bool_Type));
   end New_Counterexample_Assign;

   -----------------
   -- New_Or_Expr --
   -----------------

   function New_Or_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain)
      return W_Expr_Id
   is
   begin
      if Is_False_Boolean (Left) then
         return Right;

      elsif Is_False_Boolean (Right) then
         return Left;

      elsif Domain = EW_Pred then
         return New_Connection (Op     => EW_Or,
                                Left   => +Left,
                                Right  => +Right,
                                Domain => Domain);
      else
         return New_Call (Domain => Domain,
                          Name   => M_Boolean.Orb,
                          Args   => (1 => +Left, 2 => +Right),
                          Typ    => EW_Bool_Type);
      end if;
   end New_Or_Expr;

   function New_Or_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain;
       Base        : W_Type_Id)
       return W_Expr_Id
   is
   begin
      if Base = EW_BitVector_8_Type or else
        Base = EW_BitVector_16_Type or else
        Base = EW_BitVector_32_Type or else
        Base = EW_BitVector_64_Type or else
        Base = EW_BitVector_128_Type
      then
         return
           New_Call (Domain => Domain,
                     Name   => MF_BVs (Base).BW_Or,
                     Args   => (1 => +Left, 2 => +Right),
                     Typ    => Base);

      elsif Base = EW_Bool_Type then
         return New_Or_Expr (Left, Right, Domain);

      else
         declare
            Left2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Left,
                                            To     => EW_Bool_Type)
               else Left);
            Right2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Right,
                                            To     => EW_Bool_Type)
               else Right);
         begin
            return New_Or_Expr (Left2, Right2, Domain);
         end;
      end if;
   end New_Or_Expr;

   ----------------------
   -- New_Or_Else_Expr --
   ----------------------

   function New_Or_Else_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain)
      return W_Expr_Id
   is
   begin
      if Is_False_Boolean (Left) then
         return Right;
      elsif Is_False_Boolean (Right) then
         return Left;
      else
         if Domain = EW_Prog then
            return
              New_Connection
                (Domain => Domain,
                 Op     => EW_Or_Else,
                 Left   => Left,
                 Right  => Right);
         else
            return New_Or_Expr (Left, Right, Domain);
         end if;
      end if;
   end New_Or_Else_Expr;

   -----------------
   -- New_Or_Pred --
   -----------------

   function New_Or_Pred (Conjuncts : W_Pred_Array) return W_Pred_Id is
   begin
      if Conjuncts'Length = 0 then
         return True_Pred;

      elsif Conjuncts'Length = 1 then
         return Conjuncts (Conjuncts'First);

      else
         declare
            More : constant W_Expr_Array :=
              (for J in Conjuncts'First + 2 .. Conjuncts'Last =>
                 +Conjuncts (J));
         begin
            return New_Connection
              (Op         => EW_Or,
               Left       => Conjuncts (Conjuncts'First),
               Right      => Conjuncts (Conjuncts'First + 1),
               More_Right => More);
         end;
      end if;
   end New_Or_Pred;

   -----------------------
   -- New_Sub_VC_Marker --
   -----------------------

   function New_Sub_VC_Marker (N : Node_Id) return Symbol is
      Used_Node : Node_Id := N;
   begin
      --  String_Of_Node almost systematically prints the original node of the
      --  argument node. This is usually what we want, except in one strange
      --  case: The frontend rewrites N_And_Then Chains to lists of simple
      --  expressions, but the original node of each points to the N_And_Then,
      --  instead of the expression itself. We work around this by getting the
      --  right op of the original node in that case.

      --  ??? fix String_Of_Node instead of this workaround

      if Comes_From_Source (N)
        and then Is_Rewrite_Substitution (N)
        and then Nkind (Original_Node (N)) = N_And_Then
      then
         Used_Node := Right_Opnd (Original_Node (N));
      end if;

      return NID (GP_Pretty_Ada_Marker & Image (Integer (Used_Node), 1));
   end New_Sub_VC_Marker;

   --------------------
   -- New_Range_Expr --
   --------------------

   function New_Range_Expr
     (Domain    : EW_Domain;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id;
      Pretty    : Boolean := False)
      return W_Expr_Id
   is
      Ty : constant W_Type_Id :=
        (if Get_Type_Kind (Get_Type (Low)) = EW_Split
         then Base_Why_Type (Get_Ada_Node (+Get_Type (Low)))
         else Get_Type (Low));
      Le : constant W_Identifier_Id :=
        (if Ty = EW_Int_Type or else Why_Type_Is_Fixed (Ty) then Int_Infix_Le
         elsif Why_Type_Is_BitVector (Ty) then MF_BVs (Ty).Ule
         else MF_Floats (Ty).Le);
      Left : W_Expr_Id :=
        New_Comparison
          (Domain => Domain,
           Symbol => Le,
           Left   => Low,
           Right  => Expr);
      Right : W_Expr_Id :=
        New_Comparison
          (Domain => Domain,
           Symbol => Le,
           Left   => Expr,
           Right  => High);
   begin
      if Pretty then
         Left :=
           New_Label
             (Labels =>
                Symbol_Sets.To_Set
                  (NID (GP_Pretty_Ada_Marker & Integer'Image (Low_Bound_Id))),
              Def    => Left,
              Domain => Domain);
         Right :=
           New_Label
             (Labels =>
                Symbol_Sets.To_Set
                  (NID (GP_Pretty_Ada_Marker & Integer'Image (High_Bound_Id))),
              Def    => Right,
              Domain => Domain);
      end if;
      return
         New_And_Expr (Left, Right, Domain);
   end New_Range_Expr;

   function New_Range_Expr
     (Low, High : W_Term_Id;
      Expr      : W_Term_Id)
      return W_Pred_Id
   is
   begin
      --  ??? gnatcov complains if this is an expression function (V330-044);
      --  otherwise it could be declared in spec.
      return +W_Expr_Id'(New_Range_Expr (EW_Pred, +Low, +High, +Expr));
   end New_Range_Expr;

   ---------------------------
   -- New_Simpl_Conditional --
   ---------------------------

   function New_Simpl_Conditional
      (Condition : W_Expr_Id;
       Then_Part : W_Expr_Id;
       Else_Part : W_Expr_Id;
       Domain    : EW_Domain)
       return W_Expr_Id
   is
   begin
      if Is_True_Boolean (Condition) then
         return Then_Part;
      elsif Is_False_Boolean (Condition) then
         return Else_Part;
      else
         return
           New_Conditional
             (Condition => +Condition,
              Then_Part => Then_Part,
              Else_Part => Else_Part,
              Domain    => Domain,
              Typ       => Get_Type (Then_Part));
      end if;
   end New_Simpl_Conditional;

   -----------------------
   -- New_Temp_For_Expr --
   -----------------------

   function New_Temp_For_Expr
     (E         : W_Expr_Id;
      Need_Temp : Boolean := True)
      return W_Expr_Id
   is
   begin

      --  Internally, we use a map to store the expression for which we
      --  introduce a temporary variable. The map holds entries:
      --    Identifier -> Expr
      --  It allows us (in Binding_For_Temp) to get the expression for the temp
      --
      --  When it is not actually necessary to generate a temp for Expr, we
      --  do not introduce any binding in the map. We used to generate a
      --  binding Expr => Empty to distinguish (in Binding_For_Temp)
      --  between incorrect usage of the API and a value for which no temp was
      --  necessary. We do not anymore as we could not know how many times
      --  New_Temp_For_Expr had been called for Expr and so how long we should
      --  keep Expr => Empty in the table.
      --
      --  We always generate a temp for an expression which itself is a
      --  temporary. Otherwise we would be missing the reference the second
      --  time we call Binding_For_Temp.

      if (Need_Temp
          and then Get_Kind (+E) not in W_Identifier | W_Deref)
        or else Temp_Names_Map.Contains (+E)
      then
         declare
            Tmp : constant W_Expr_Id :=
              +New_Temp_Identifier (Ada_Node => Get_Ada_Node (+E),
                                    Typ      => Get_Type (E));
         begin
            Temp_Names_Map.Insert (+Tmp, +E);
            return Tmp;
         end;
      else
         return E;
      end if;
   end New_Temp_For_Expr;

   -----------------------
   -- New_Typed_Binding --
   -----------------------

   function New_Typed_Binding
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Identifier_Id;
      Def      : W_Expr_Id;
      Context  : W_Expr_Id)
      return W_Expr_Id
   is
   begin
      return
        New_Binding
          (Ada_Node, Domain, Name, Def, Context, Get_Type (Context));
   end New_Typed_Binding;

   -----------------------
   -- New_Function_Call --
   -----------------------

   function New_Function_Call
     (Ada_Node : Node_Id := Empty;
      Subp     : Node_Id;
      Selector : Selection_Kind := Why.Inter.Standard;
      Name     : W_Identifier_Id;
      Args     : W_Expr_Array;
      Check    : Boolean;
      Domain   : EW_Domain;
      Typ      : W_Type_Id)
      return W_Expr_Id
   is
   begin
      if Check then
         pragma Assert (Domain = EW_Prog);
         return New_VC_Expr (Ada_Node => Ada_Node,
                             Reason   => VC_Precondition,
                             Expr     => New_Call
                               (Name     => Name,
                                Args     => Args,
                                Ada_Node => Ada_Node,
                                Domain   => Domain,
                                Typ      => Typ),
                             Domain   => Domain);

      elsif Domain = EW_Prog
        or else not Use_Guard_For_Function (Subp)
      then
         return New_Call
           (Name     => Name,
            Args     => Args,
            Ada_Node => Ada_Node,
            Domain   => Domain,
            Typ      => Typ);
      else

         --  Here we do not call directly the logic function introduced for
         --  Subp as its postcondition is not axiomatized. We rather use the
         --  post predicate associated to Subp to assume the necessary
         --  constraints on its result. We generate:
         --   (epsilon result : t. result = f args /\ post_pred result args)
         --      in the term domain
         --   (let result = f args in assume {post_pred result args}; result)
         --      in the pterm domain

         if Domain = EW_Pterm then
            declare
               Result_Id  : constant W_Identifier_Id :=
                 New_Temp_Identifier
                   (Base_Name => "result", Typ => Typ);
               Arg_Tmps   : W_Expr_Array (Args'Range);
               Result     : W_Prog_Id;

            begin
               --  The arguments of the call are program terms. We introduce
               --  identifiers for them so they can be used in the post
               --  predicate.

               for I in Args'Range loop
                  Arg_Tmps (I) := New_Temp_For_Expr (Args (I));
               end loop;

               Result := Sequence
                 (Left  => New_Assume_Statement
                    (Pred => New_Call
                         (Name     => Guard_Predicate_Name (Subp, Selector),
                          Args     => +Result_Id & Arg_Tmps,
                          Ada_Node => Ada_Node,
                          Typ      => EW_Bool_Type)),
                  Right => +Result_Id);

               Result := New_Binding
                 (Ada_Node => Ada_Node,
                  Name     => Result_Id,
                  Def      => New_Call
                    (Name     => Name,
                     Args     => Arg_Tmps,
                     Ada_Node => Ada_Node,
                     Typ      => Typ),
                  Context  => Result,
                  Typ      => Typ);

               --  Introduce bindings for the temporary identifiers for the
               --  arguments.

               for Arg_Tmp of Arg_Tmps loop
                  Result := +Binding_For_Temp
                    (Domain  => EW_Pterm,
                     Tmp     => Arg_Tmp,
                     Context => +Result);
               end loop;

               return +Result;
            end;
         else
            declare
               Result_Id : constant W_Identifier_Id :=
                 New_Temp_Identifier
                   (Base_Name => "result", Typ => Typ);
               Pred_Call : W_Pred_Id;
               Arg_Tmps  : W_Expr_Array (Args'Range);
               Result    : W_Term_Id;

            begin
               --  Introduce temporary variables for the parameters to avoid
               --  introducing an exponential blow-up in case of nested calls.

               for I in Args'Range loop
                  Arg_Tmps (I) := New_Temp_For_Expr (Args (I));
               end loop;

               Pred_Call := New_Call
                 (Name     => Guard_Predicate_Name (Subp, Selector),
                  Args     => +Result_Id & Arg_Tmps,
                  Ada_Node => Ada_Node,
                  Typ      => EW_Bool_Type);

               Result := New_Epsilon
                 (Name   => Result_Id,
                  Typ    => Typ,
                  Pred   => New_And_Pred
                    (New_Comparison
                         (Symbol => Why_Eq,
                          Left   => +Result_Id,
                          Right  => New_Call
                            (Name     => Name,
                             Args     => Arg_Tmps,
                             Ada_Node => Ada_Node,
                             Typ      => Typ)),
                     Pred_Call));

               --  Introduce bindings for the temporary identifiers for the
               --  arguments.

               for Arg_Tmp of Arg_Tmps loop
                  Result := +Binding_For_Temp
                    (Domain  => EW_Term,
                     Tmp     => Arg_Tmp,
                     Context => +Result);
               end loop;

               return +Result;
            end;
         end if;
      end if;
   end New_Function_Call;

   -----------------------
   -- New_Operator_Call --
   -----------------------

   function New_Operator_Call
     (Ada_Node   : Node_Id;
      Name       : W_Identifier_Id;
      Fix_Name   : Boolean := False;
      Args       : W_Expr_Array;
      Reason     : VC_Kind;
      Check      : Boolean;
      Domain     : EW_Domain;
      Typ        : W_Type_Id;
      Check_Info : Check_Info_Type := New_Check_Info)
      return W_Expr_Id
   is
      Name_Spec : constant W_Identifier_Id :=
        (if Check and not Fix_Name then To_Program_Space (Name) else Name);
      Call : constant W_Expr_Id :=
        New_Call (Ada_Node => Ada_Node,
                  Name     => Name_Spec,
                  Args     => Args,
                  Domain   => Domain,
                  Typ      => Typ);
   begin
      if Check then
         return New_VC_Expr (Ada_Node   => Ada_Node,
                             Reason     => Reason,
                             Expr       => Call,
                             Check_Info => Check_Info,
                             Domain     => Domain);
      else
         return Call;
      end if;
   end New_Operator_Call;

   -----------------
   -- New_VC_Call --
   -----------------

   function New_VC_Call
     (Ada_Node   : Node_Id;
      Name       : W_Identifier_Id;
      Progs      : W_Expr_Array;
      Reason     : VC_Kind;
      Typ        : W_Type_Id;
      Check_Info : Check_Info_Type := New_Check_Info)
      return W_Prog_Id
   is
      Call : constant W_Prog_Id :=
        New_Call (Ada_Node => Ada_Node,
                  Name     => Name,
                  Args     => Progs,
                  Typ      => Typ);
   begin
      return New_VC_Prog (Ada_Node   => Ada_Node,
                          Reason     => Reason,
                          Check_Info => Check_Info,
                          Expr       => Call);
   end New_VC_Call;

   -----------------
   -- New_VC_Expr --
   -----------------

   function New_VC_Expr
     (Ada_Node   : Node_Id;
      Expr       : W_Expr_Id;
      Reason     : VC_Kind;
      Domain     : EW_Domain;
      Check_Info : Check_Info_Type := New_Check_Info)
      return W_Expr_Id
   is
   begin
      return
        Insert_Cnt_Loc_Label
          (Ada_Node => Ada_Node,
           E        =>
             New_Label
               (Ada_Node => Ada_Node,
                Labels   => New_VC_Labels (Ada_Node, Reason, Check_Info),
                Def      => Expr,
                Domain   => Domain,
                Typ      => Get_Type (Expr)));
   end New_VC_Expr;

   -------------------
   -- New_VC_Labels --
   -------------------

   function New_VC_Labels
     (N          : Node_Id;
      Reason     : VC_Kind;
      Check_Info : Check_Info_Type) return Symbol_Set
   is
      --  A GNATprove label in Why3 has the following form
      --
      --  "GP_Reason:VC_Kind"     - the kind of the VC
      --  "GP_Sloc:file:line:col" - the sloc of the construct that triggers the
      --   VC
      --  "keep_on_simp"          - tag that disallows simplifying this VC away
      --  "model_vc"              - identifies the construct that triggers the
      --   VC and it is not postcondition (for generating counterexamples)
      --  "model_vc_post"         - identifies the construct that triggers the
      --   VC and is postcondition (for generating counterexamples)
      --
      --  For a node inside an instantiation, we use the location of the
      --  top-level instantiation. This could be refined in the future.

      Sloc : constant Source_Ptr := Compute_VC_Sloc
        (N, Left_Most => Locate_On_First_Token (Reason));
      Id   : constant VC_Id := Register_VC
        (N, Reason, Current_Subp, Check_Info);

      Labels : Symbol_Set;

   begin
      Labels.Insert (New_Check_Label (Sloc, Reason, Id));

      declare
         Symb : constant Symbol := New_Shape_Label (Node => N);
      begin
         if Symb /= No_Symbol then
            Labels.Insert (Symb);
         end if;
      end;

      if Reason = VC_Postcondition then
         Labels.Insert (Model_VC_Post);
      else
         Labels.Insert (VC_Annotation);
      end if;

      return Labels;
   end New_VC_Labels;

   ------------------
   -- New_Xor_Expr --
   ------------------

   function New_Xor_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain;
       Base        : W_Type_Id)
       return W_Expr_Id
   is
   begin
      if Base = EW_BitVector_8_Type or else
        Base = EW_BitVector_16_Type or else
        Base = EW_BitVector_32_Type or else
        Base = EW_BitVector_64_Type or else
        Base = EW_BitVector_128_Type
      then
         return
           New_Call (Domain => Domain,
                     Name   => MF_BVs (Base).BW_Xor,
                     Args   => (1 => +Left, 2 => +Right),
                     Typ    => Base);

      else
         declare
            Left2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Left,
                                            To     => EW_Bool_Type)
               else Left);
            Right2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Right,
                                            To     => EW_Bool_Type)
               else Right);
            Or_Expr : constant W_Expr_Id :=
              New_Or_Expr (Left2, Right2, Domain);
            Both_Expr : constant W_Expr_Id :=
              New_And_Expr (Left2, Right2, Domain);
            Not_Both_Expr : constant W_Expr_Id :=
              (if Domain = EW_Pred then
                  New_Not (Domain => Domain, Right => Both_Expr)
               else
                  New_Call (Domain => Domain,
                            Name   => M_Boolean.Notb,
                            Args   => (1 => Both_Expr),
                            Typ    => EW_Bool_Type));
         begin
            return New_And_Expr (Or_Expr, Not_Both_Expr, Domain);
         end;
      end if;
   end New_Xor_Expr;

   --------------------------
   -- Pred_Of_Boolean_Term --
   --------------------------

   function Pred_Of_Boolean_Term (W : W_Term_Id) return W_Pred_Id is
     (New_Call (Name => Why_Eq,
                Args => (1 => +W, 2 => +Bool_True (EW_Term)),
                Typ  => EW_Bool_Type));

   ------------
   -- To_Int --
   ------------

   function To_Int (D : EW_Domain; E : W_Expr_Id) return W_Expr_Id is
   begin
      return
        Insert_Scalar_Conversion (Domain => D, Expr => E, To => EW_Int_Type);
   end To_Int;

   --------------------------
   -- Transform_Compare_Op --
   --------------------------

   function Transform_Compare_Op
     (Op     : N_Op_Compare;
      Ty     : W_Type_Id;
      Domain : EW_Domain)
      return W_Identifier_Id is
   begin
      if Domain = EW_Term then
         if Ty in EW_Int_Type | EW_Bool_Type
           or else Why_Type_Is_Fixed (Ty)
         then
            case Op is
               when N_Op_Gt => return M_Integer.Bool_Gt;
               when N_Op_Lt => return M_Integer.Bool_Lt;
               when N_Op_Eq => return M_Integer.Bool_Eq;
               when N_Op_Ne => return M_Integer.Bool_Ne;
               when N_Op_Ge => return M_Integer.Bool_Ge;
               when N_Op_Le => return M_Integer.Bool_Le;
            end case;
         elsif Why_Type_Is_Float (Ty) then
            case Op is
               when N_Op_Gt => return MF_Floats (Ty).Bool_Gt;
               when N_Op_Lt => return MF_Floats (Ty).Bool_Lt;
               when N_Op_Eq => return MF_Floats (Ty).Bool_Eq;
               when N_Op_Ne => return MF_Floats (Ty).Bool_Ne;
               when N_Op_Ge => return MF_Floats (Ty).Bool_Ge;
               when N_Op_Le => return MF_Floats (Ty).Bool_Le;
            end case;
         elsif Why_Type_Is_BitVector (Ty) then
            case Op is
               when N_Op_Gt => return MF_BVs (Ty).Bool_Gt;
               when N_Op_Lt => return MF_BVs (Ty).Bool_Lt;
               when N_Op_Eq => return MF_BVs (Ty).Bool_Eq;
               when N_Op_Ne => return MF_BVs (Ty).Bool_Ne;
               when N_Op_Ge => return MF_BVs (Ty).Bool_Ge;
               when N_Op_Le => return MF_BVs (Ty).Bool_Le;
            end case;
         else
            raise Program_Error;
         end if;
      elsif Ty in EW_Int_Type | EW_Bool_Type
           or else Why_Type_Is_Fixed (Ty)
      then
         case Op is
            when N_Op_Gt => return Int_Infix_Gt;
            when N_Op_Lt => return Int_Infix_Lt;
            when N_Op_Eq => return Why_Eq;
            when N_Op_Ne => return Why_Neq;
            when N_Op_Ge => return Int_Infix_Ge;
            when N_Op_Le => return Int_Infix_Le;
         end case;
      elsif Why_Type_Is_Float (Ty) then
         case Op is
            when N_Op_Gt => return MF_Floats (Ty).Gt;
            when N_Op_Lt => return MF_Floats (Ty).Lt;
            when N_Op_Eq => return MF_Floats (Ty).Eq;
            when N_Op_Ne => return MF_Floats (Ty).Neq;
            when N_Op_Ge => return MF_Floats (Ty).Ge;
            when N_Op_Le => return MF_Floats (Ty).Le;
         end case;
      elsif Why_Type_Is_BitVector (Ty) then
         case Op is
            when N_Op_Gt => return MF_BVs (Ty).Ugt;
            when N_Op_Lt => return MF_BVs (Ty).Ult;
            when N_Op_Eq =>
               if Domain = EW_Pred then
                  return Why_Eq;
               else
                  return MF_BVs (Ty).Prog_Eq;
               end if;
            when N_Op_Ne =>
               if Domain = EW_Pred then
                  return Why_Neq;
               else
                  return MF_BVs (Ty).Prog_Neq;
               end if;
            when N_Op_Ge => return MF_BVs (Ty).Uge;
            when N_Op_Le => return MF_BVs (Ty).Ule;
         end case;
      else
         raise Program_Error;
      end if;
   end Transform_Compare_Op;

   --------------------------------------------
   -- Transform_Non_Binary_Modular_Operation --
   --------------------------------------------

   function Transform_Non_Binary_Modular_Operation
     (Ada_Node   : Node_Id;
      Ada_Type   : Type_Kind_Id;
      Domain     : EW_Domain;
      Op         : N_Op;
      Left_Opnd  : W_Expr_Id := Why_Empty;
      Right_Opnd : W_Expr_Id;
      Rep_Type   : W_Type_Id;
      Modulus    : Uint)
      return W_Expr_Id
   is
      T : W_Expr_Id;

   begin
      --  GNAT only supports non-binary modulus up to 2**32. We use this
      --  limitation here to simplify the implementation, so we check this
      --  is the case here.

      if Modulus >= UI_Expon (2, 32) then
         raise Program_Error;
      end if;

      case Op is

         --  Transform (-Y) into:
         --    (Modulus - Y) modulo Modulus
         --  We add the extra modulo in order to deal with the special case
         --  of -0. We use modulo instead of a test in order to have a fully
         --  computational interpretation.

         when N_Op_Minus =>
            pragma Assert (Left_Opnd = Why_Empty);

            declare
               Modulus_Expr : constant W_Expr_Id :=
                 New_Modular_Constant
                   (Value => Modulus,
                    Typ   => Rep_Type);

               Sub : constant W_Expr_Id :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => MF_BVs (Rep_Type).Sub,
                    Args     =>
                      (1 => Modulus_Expr,
                       2 => Right_Opnd),
                    Typ      => Rep_Type);

            begin
               T := New_Call (Domain => Domain,
                              Name   => MF_BVs (Rep_Type).Urem,
                              Args   =>
                                (1 => Sub,
                                 2 => Modulus_Expr),
                              Typ    => Rep_Type);
            end;

         --  Transform (X + Y) into:
         --    if Modulus - X <= Y
         --    then (X + Y) - Modulus
         --    else X + Y

         when N_Op_Add =>
            declare
               BV            : constant M_BV_Type := MF_BVs (Rep_Type);
               Modulus_Expr  : constant W_Expr_Id :=
                 New_Modular_Constant (Value => Modulus,
                                       Typ   => Rep_Type);
               Add_Expr      : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Add,
                           Args     => (1 => Left_Opnd,
                                        2 => Right_Opnd),
                           Typ   => Rep_Type);
               Add_Id        : constant W_Expr_Id :=
                 New_Temp_For_Expr (E => Add_Expr);
               Overflow_Test : constant W_Expr_Id :=
                 New_Call (Domain => Domain,
                           Name   => BV.Ule,
                           Args   =>
                             (1 => New_Call (Domain => Domain,
                                             Name   => BV.Sub,
                                             Args   => (1 => Modulus_Expr,
                                                        2 => Left_Opnd),
                                             Typ    => Rep_Type),
                              2 => Right_Opnd),
                           Typ    => EW_Bool_Type);
               Modulo_Expr   : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Sub,
                           Args     => (1 => Add_Id,
                                        2 => Modulus_Expr),
                           Typ      => Rep_Type);
               Ite_Expr      : constant W_Conditional_Id :=
                 New_Conditional (Ada_Node    => Ada_Node,
                                  Domain      => Domain,
                                  Condition   => Overflow_Test,
                                  Then_Part   => Modulo_Expr,
                                  Else_Part   => Add_Id,
                                  Typ         => Rep_Type);
            begin
               T := Binding_For_Temp (Ada_Node => Ada_Node,
                                      Domain   => Domain,
                                      Tmp      => Add_Id,
                                      Context  => +Ite_Expr);
            end;

         --  Transform (X - Y) into:
         --    if Y > X
         --    then (X - Y) + Modulus
         --    else X - Y

         when N_Op_Subtract =>
            declare
               BV            : constant M_BV_Type := MF_BVs (Rep_Type);
               Modulus_Expr  : constant W_Expr_Id :=
                 New_Modular_Constant (Value => Modulus,
                                       Typ   => Rep_Type);
               Sub_Expr      : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Sub,
                           Args     => (1 => Left_Opnd,
                                        2 => Right_Opnd),
                           Typ   => Rep_Type);
               Sub_Id        : constant W_Expr_Id :=
                 New_Temp_For_Expr (E => Sub_Expr);
               Overflow_Test : constant W_Expr_Id :=
                 New_Call (Domain   => Domain,
                           Name     => BV.Ult,
                           Args     => (1 => Left_Opnd,
                                        2 => Right_Opnd),
                           Typ      => EW_Bool_Type);
               Modulo_Expr   : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Add,
                           Args     => (1 => Sub_Id,
                                        2 => Modulus_Expr),
                           Typ      => Rep_Type);
               Ite_Expr      : constant W_Conditional_Id :=
                 New_Conditional (Ada_Node    => Ada_Node,
                                  Domain      => Domain,
                                  Condition   => Overflow_Test,
                                  Then_Part   => Modulo_Expr,
                                  Else_Part   => Sub_Id,
                                  Typ         => Rep_Type);
            begin
               T := Binding_For_Temp (Ada_Node => Ada_Node,
                                      Domain   => Domain,
                                      Tmp      => Sub_Id,
                                      Context  => +Ite_Expr);
            end;

         --  In those cases where the multiplication may not fit in the size of
         --  bitvector of [Rep_Type], convert both operands to the next size of
         --  bitvector, do the multiplication without overflow in that larger
         --  type, then apply the modulus and convert back to the original
         --  type.

         when N_Op_Multiply =>
            declare
               Next_Bv      : constant W_Type_Id :=
                 (if Modulus < UI_Expon (2, 8) then
                    (if Modular_Size (Ada_Type) < 16 then EW_BitVector_16_Type
                     else Rep_Type)
                  elsif Modulus < UI_Expon (2, 16) then
                    (if Modular_Size (Ada_Type) < 32 then EW_BitVector_32_Type
                     else Rep_Type)
                  elsif Modulus < UI_Expon (2, 32) then
                    EW_BitVector_64_Type
                  else
                    --  GNAT does not support non-binary modulus greater than
                    --  2**32, which we check conservatively here.
                    raise Program_Error);
               Modulus_Expr : constant W_Expr_Id :=
                 New_Modular_Constant (Value => Modulus,
                                       Typ   => Next_Bv);
               Next_Left    : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Domain => Domain,
                                           Expr   => Left_Opnd,
                                           To     => Next_Bv);
               Next_Right   : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Domain => Domain,
                                           Expr   => Right_Opnd,
                                           To     => Next_Bv);
               Mul_Expr     : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => MF_BVs (Next_Bv).Mult,
                           Args     => (1 => Next_Left,
                                        2 => Next_Right),
                           Typ      => Next_Bv);
               Modulo_Expr  : constant W_Expr_Id :=
                 New_Call (Name   => MF_BVs (Next_Bv).Urem,
                           Domain => Domain,
                           Args   => (1 => Mul_Expr,
                                      2 => Modulus_Expr),
                           Typ    => Next_Bv);
            begin
               T := Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                              Domain   => Domain,
                                              Expr     => Modulo_Expr,
                                              To       => Rep_Type);
            end;

         --  Translate exponentiation on mathematical integers to avoid
         --  the wrap-around semantics on bitvector types. Indeed, it is not
         --  possible to go to a bigger bitvector type here as there are no
         --  such bitvector type even for 8 bit bitvectors.

         when N_Op_Expon =>
            declare
               Modulus_Expr : constant W_Expr_Id :=
                 New_Integer_Constant (Value => Modulus);
               Int_Left     : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Domain => Domain,
                                           Expr   => Left_Opnd,
                                           To     => EW_Int_Type);
               Exp_Expr     : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => M_Int_Power.Power,
                           Args     => (1 => Int_Left,
                                        2 => Right_Opnd),
                           Typ      => EW_Int_Type);
               Modulo_Expr  : constant W_Expr_Id :=
                 New_Call (Name   => M_Int_Div.Rem_Id,
                           Domain => Domain,
                           Args   => (1 => Exp_Expr,
                                      2 => Modulus_Expr),
                           Typ    => EW_Int_Type);
            begin
               T := Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                              Domain   => Domain,
                                              Expr     => Modulo_Expr,
                                              To       => Rep_Type);
            end;

         when others =>
            raise Program_Error;
      end case;

      return T;
   end Transform_Non_Binary_Modular_Operation;

   -----------------------
   -- Why_Default_Value --
   -----------------------

   function Why_Default_Value
     (Domain : EW_Domain;
      E      : Type_Kind_Id)
      return W_Expr_Id
   is
      Why_Ent : constant Entity_Id :=
        Get_Ada_Node (+EW_Abstract (E));
   begin
      if Is_Standard_Boolean_Type (E) then
         return New_Literal (Domain => Domain, Value => EW_True);
      else
         return +E_Symb (Why_Ent, WNE_Dummy);
      end if;
   end Why_Default_Value;

end Why.Gen.Expr;
