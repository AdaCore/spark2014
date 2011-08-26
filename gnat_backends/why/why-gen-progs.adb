------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R O G S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Atree;               use Atree;
with Einfo;               use Einfo;
with Uintp;               use Uintp;

with Why.Conversions;     use Why.Conversions;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Preds;       use Why.Gen.Preds;

package body Why.Gen.Progs is

   function Convert_From_Scalar
      (Ada_Node : Node_Id := Empty;
       From     : Why_Scalar_Enum;
       To       : Why_Type;
       Why_Expr : W_Prog_Id;
       Reason   : VC_Kind := VC_Range_Check) return W_Prog_Id;
   --  Convert the Why expression in argument to scalar "int"/"real".
   --  It is expected to be of type "To".

   function Convert_To_Scalar
      (Ada_Node : Node_Id := Empty;
       From     : Why_Type;
       To       : Why_Scalar_Enum;
       Why_Expr : W_Prog_Id) return W_Prog_Id;
   --  Convert the Why expression in argument to scalar "int"/"real".
   --  It is expected to be of type "From".

   function Insert_Array_Conversion
      (Ada_Node : Node_Id := Empty;
       To       : Why_Type;
       From     : Why_Type;
       Why_Expr : W_Prog_Id) return W_Prog_Id;

   function Insert_Scalar_Conversion
      (Ada_Node   : Node_Id := Empty;
       Kind       : Why_Scalar_Enum;
       To         : Why_Type;
       From       : Why_Type;
       Why_Expr   : W_Prog_Id;
       Base_Type  : Why_Type) return W_Prog_Id;

   function Is_False_Boolean (P : W_Expr_Id) return Boolean;
   --  Check if the given program is the program "false"

   function Is_True_Boolean (P : W_Expr_Id) return Boolean;
   --  Check if the given program is the program "true"

   ---------------------
   -- Conversion_Name --
   ---------------------

   function Conversion_Name
      (From : Why_Type;
       To   : Why_Type) return W_Identifier_Id
   is
   begin
      case From.Kind is
         when Why_Scalar_Enum =>
            case To.Kind is
               when Why_Scalar_Enum =>

                  --  Only certain conversions are OK

                  if From.Kind = Why_Int and then To.Kind = Why_Real then
                     return Real_Of_Int.Id;
                  elsif From.Kind = Why_Bool and then To.Kind = Why_Int then
                     return Int_Of_Bool.Id;
                  else

                     --  either the two objects are of the same type
                     --  (in which case the conversion is useless) or
                     --  they are of incompatible types
                     --  In both cases, it is an error.

                     raise Program_Error;
                  end if;

               when Why_Abstract =>
                  return
                     Conversion_From.Id
                       (Full_Name (To.Wh_Abstract),
                        Why_Scalar_Type_Name (From.Kind));
            end case;
         when Why_Abstract =>
            case To.Kind is
               when Why_Scalar_Enum =>
                  return
                    Conversion_To.Id (Full_Name (From.Wh_Abstract),
                                      Why_Scalar_Type_Name (To.Kind));
               when Why_Abstract =>
                  raise Program_Error
                     with "Conversion between arbitrary types attempted";
            end case;
      end case;
   end Conversion_Name;

   -----------------------
   -- Convert_To_Scalar --
   -----------------------

   function Convert_To_Scalar
      (Ada_Node : Node_Id := Empty;
       From     : Why_Type;
       To       : Why_Scalar_Enum;
       Why_Expr : W_Prog_Id) return W_Prog_Id is
   begin
      return
        New_Call
        (Ada_Node => Ada_Node,
         Name     => Conversion_Name (From => From,
                                      To => Why_Types (To)),
         Args     => (1 => +Why_Expr));
   end Convert_To_Scalar;

   -------------------------
   -- Convert_From_Scalar --
   -------------------------

   function Convert_From_Scalar
      (Ada_Node : Node_Id := Empty;
       From     : Why_Scalar_Enum;
       To       : Why_Type;
       Why_Expr : W_Prog_Id;
       Reason   : VC_Kind := VC_Range_Check) return W_Prog_Id
   is
   begin
      return
        New_Located_Call
          (Ada_Node => Ada_Node,
           Name     =>
            To_Program_Space
              (Conversion_Name (From => Why_Types (From), To => To)),
           Progs    => (1 => +Why_Expr),
           Reason   => Reason);
   end Convert_From_Scalar;

   -----------------------------
   -- Insert_Array_Conversion --
   -----------------------------

   function Insert_Array_Conversion
      (Ada_Node : Node_Id := Empty;
       To       : Why_Type;
       From     : Why_Type;
       Why_Expr : W_Prog_Id) return W_Prog_Id
   is
      Ada_To   : constant Node_Id := To.Wh_Abstract;
      Ada_From : constant Node_Id := From.Wh_Abstract;
   begin
      return
        New_Call
          (Ada_Node => Ada_Node,
           Name     => Array_Conv_To.Id (Full_Name (Ada_To)),
           Args     =>
             (1 =>
                New_Call
                  (Ada_Node => Ada_Node,
                   Name     => Array_Conv_From.Id (Full_Name (Ada_From)),
                   Args     => (1 => +Why_Expr))));
   end Insert_Array_Conversion;

   -----------------------
   -- Insert_Conversion --
   -----------------------

   function Insert_Conversion
      (Ada_Node  : Node_Id := Empty;
       To        : Why_Type;
       From      : Why_Type;
       Why_Expr  : W_Prog_Id;
       Base_Type : Why_Type := Why_Int_Type) return W_Prog_Id
   is
   begin
      --  In this particular case, we do nothing
      if Base_Type.Kind in Why_Scalar_Enum and then To = From then
         return Why_Expr;
      end if;

      --  We check the 'To' type, and there are four cases.
      --    * Why_Int => Integer conversion
      --    * Why_Real => Real conversion
      --    * Ada Integer type => Integer conversion
      --    * Ada Array type => Array conversion
      --    * other Ada type kind => failure
      case To.Kind is
         when Why_Scalar_Enum =>
            return
               Insert_Scalar_Conversion
                  (Ada_Node, To.Kind, To, From, Why_Expr, Base_Type);

         when Why_Abstract =>
            declare
               Ada_Type : constant Node_Id := To.Wh_Abstract;
            begin
               case Ekind (Ada_Type) is
                  when Discrete_Kind =>
                     return
                        Insert_Scalar_Conversion
                           (Ada_Node, Why_Int,
                            To, From, Why_Expr, Base_Type);

                  when Float_Kind =>
                     return
                        Insert_Scalar_Conversion
                           (Ada_Node, Why_Real,
                            To, From, Why_Expr, Base_Type);

                  when Array_Kind =>
                     return
                        Insert_Array_Conversion
                           (Ada_Node, To, From, Why_Expr);

                  when others =>
                     raise Not_Implemented;

               end case;
            end;

      end case;

   end Insert_Conversion;

   ------------------------------
   -- Insert_Scalar_Conversion --
   ------------------------------

   function Insert_Scalar_Conversion
      (Ada_Node  : Node_Id := Empty;
       Kind      : Why_Scalar_Enum;
       To        : Why_Type;
       From      : Why_Type;
       Why_Expr  : W_Prog_Id;
       Base_Type : Why_Type) return W_Prog_Id
   is
   begin
      if To.Kind in Why_Scalar_Enum then
         --  We convert to "int"
         if Base_Type.Kind /= Why_Int and then From.Kind = To.Kind then
            --  If both types are scalar, and we have a Base_Type, insert a
            --  conversion
            return
               Convert_To_Scalar
                 (Ada_Node => Ada_Node,
                  From     => Base_Type,
                  To       => To.Kind,
                  Why_Expr =>
                     Convert_From_Scalar
                        (Ada_Node => Ada_Node,
                         From     => From.Kind,
                         To       => Base_Type,
                         Why_Expr => Why_Expr,
                         Reason   => VC_Overflow_Check));
         else
            return Convert_To_Scalar (Ada_Node, From, To.Kind, Why_Expr);
         end if;

      elsif From.Kind in Why_Scalar_Enum then
         return Convert_From_Scalar (Ada_Node, From.Kind, To, Why_Expr);
      else
         return
            Insert_Scalar_Conversion
               (Ada_Node => Ada_Node,
                Kind     => Kind,
                To       => To,
                From     => Why_Types (Kind),
                Why_Expr =>
                  Insert_Scalar_Conversion
                    (Ada_Node  => Ada_Node,
                     Kind      => Kind,
                     To        => Why_Types (Kind),
                     From      => From,
                     Why_Expr  => Why_Expr,
                     Base_Type => Why_Types (Kind)),
                Base_Type => Why_Types (Kind));
      end if;
   end Insert_Scalar_Conversion;

   ----------------------
   -- Is_False_Boolean --
   ----------------------

   function Is_False_Boolean (P : W_Expr_Id) return Boolean
   is
   begin
      return
         (Get_Kind (+P) = W_Literal and then
          Literal_Get_Value (W_Literal_Id (P)) = EW_False);
   end Is_False_Boolean;

   ---------------------
   -- Is_True_Boolean --
   ---------------------

   function Is_True_Boolean (P : W_Expr_Id) return Boolean
   is
   begin
      return
         (Get_Kind (+P) = W_Literal and then
          Literal_Get_Value (W_Literal_Id (P)) = EW_True);
   end Is_True_Boolean;

   --------------------------
   -- New_Assume_Statement --
   --------------------------

   function New_Assume_Statement
      (Ada_Node    : Node_Id;
       Pred        : W_Predicate_Id;
       Return_Type : W_Primitive_Type_Id :=
                       New_Base_Type (Base_Type => EW_Unit))
      return W_Prog_Id
   is
   begin
      return
        New_Any_Expr
          (Ada_Node => Ada_Node,
           Any_Type =>
             New_Computation_Type
               (Ada_Node => Ada_Node,
                Result   => New_Result (+Return_Type),
                Effects  => New_Effects,
                Post     => Pred));
   end New_Assume_Statement;

   ------------------
   -- New_For_Loop --
   ------------------

   function New_For_Loop
     (Ada_Node   : Node_Id;
      Loop_Index : W_Identifier_Id;
      Low        : W_Identifier_Id;
      High       : W_Identifier_Id;
      Invariant  : W_Predicate_Id;
      Loop_Body  : W_Prog_Id) return W_Prog_Id
   is
      Index_Deref  : constant W_Prog_Id :=
                       New_Unary_Op
                         (Ada_Node => Ada_Node,
                          Op       => EW_Deref,
                          Right    => +Loop_Index);
      Addition     : constant W_Prog_Id :=
                       New_Binary_Op
                         (Ada_Node => Ada_Node,
                          Op       => EW_Add,
                          Op_Type  => EW_Int,
                          Left     => +Index_Deref,
                          Right    =>
                            New_Integer_Constant
                              (Ada_Node => Ada_Node,
                               Value    => Uint_1));
      Incr_Stmt    : constant W_Prog_Id :=
                       New_Assignment
                         (Ada_Node => Ada_Node,
                          Name     => Loop_Index,
                          Value    => Addition);
      Loop_Cond    : constant W_Prog_Id  :=
                       New_Relation
                         (Ada_Node => Ada_Node,
                          Op       => EW_Le,
                          Left     => Index_Deref,
                          Right    => +High);
      Loop_Content : constant W_Prog_Id :=
                       New_Statement_Sequence
                         (Ada_Node   => Ada_Node,
                          Statements => (1 => Loop_Body, 2 => Incr_Stmt));
      Enriched_Inv : constant W_Predicate_Id :=
                       New_Connection
                         (Domain => EW_Term,
                          Op     => EW_Or,
                          Left   => +Invariant,
                          Right  =>
                            New_Relation
                              (Left   => +Low,
                               Op     => EW_Le,
                               Right  => +Loop_Index,
                               Op2    => EW_Le,
                               Right2 =>
                                 New_Binary_Op
                                   (Op      => EW_Add,
                                    Op_Type => EW_Int,
                                    Left    => +High,
                                    Right   =>
                                      New_Integer_Constant
                                        (Value => Uint_1))));
   begin
      return
        New_Binding_Ref
          (Ada_Node => Ada_Node,
           Name     => Loop_Index,
           Def      => +Low,
           Context  =>
             New_While_Loop
                (Ada_Node     => Ada_Node,
                 Condition    => Loop_Cond,
                 Annotation   =>
                   New_Loop_Annot
                     (Invariant =>
                        +New_Located_Expr
                          (Ada_Node => Ada_Node,
                           Expr     => +Enriched_Inv,
                           Reason   => VC_Loop_Invariant,
                           Domain   => EW_Pred)),
                 Loop_Content => Loop_Content));
   end New_For_Loop;

   ----------------
   -- New_Ignore --
   ----------------

   function New_Ignore (Ada_Node : Node_Id := Empty; Prog : W_Prog_Id)
      return W_Prog_Id
   is
   begin
      return
        New_Call
          (Ada_Node => Ada_Node,
           Name     => New_Ignore_Name.Id,
           Args     => (1 => +Prog));
   end New_Ignore;

   ------------------------
   -- New_Located_Assert --
   ------------------------

   function New_Located_Assert
      (Ada_Node : Node_Id;
       Pred     : W_Predicate_Id) return W_Prog_Id
   is
   begin
      return
        New_Assert
          (Ada_Node => Ada_Node,
           Pred     =>
             +New_Located_Expr
               (Ada_Node => Ada_Node,
                Expr     => +Pred,
                Reason   => VC_Assert,
                Domain   => EW_Pred));
   end New_Located_Assert;

   ----------------------
   -- New_Located_Call --
   ----------------------

   function New_Located_Call
      (Ada_Node : Node_Id;
       Name     : W_Identifier_Id;
       Progs    : W_Expr_Array;
       Reason   : VC_Kind) return W_Prog_Id
   is
   begin
      return
        +New_Located_Expr
          (Ada_Node => Ada_Node,
           Reason   => Reason,
           Expr =>
             New_Call
               (Ada_Node => Ada_Node,
                Name     => Name,
                Args     => Progs,
                Domain   => EW_Prog),
           Domain => EW_Prog);
   end New_Located_Call;

   ------------------
   -- New_And_Expr --
   ------------------

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id is
   begin
      if Is_True_Boolean (+Left) then
         return Right;

      elsif Is_True_Boolean (+Right) then
         return Left;

      else
         if Domain = EW_Pred then
            return New_Connection
              (Op    => EW_And,
               Left  => +Left,
               Right => +Right);
         else
            return
              New_Call
                (Domain => Domain,
                 Name   => New_Identifier ("bool_and"),
                 Args   => (1 => +Left, 2 => +Right));
         end if;
      end if;
   end New_And_Expr;

   -----------------------
   -- New_And_Then_Expr --
   -----------------------

   function New_And_Then_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id is
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

   --------------------
   -- New_Comparison --
   --------------------

   function New_Comparison
     (Cmp         : EW_Relation;
      Left, Right : W_Expr_Id;
      Domain      : EW_Domain)
     return W_Expr_Id is
   begin
      if Domain in EW_Pred | EW_Prog then
         return
            New_Relation
              (Domain   => Domain,
               Left     => +Left,
               Right    => +Right,
               Op       => Cmp);
      else
         return
           New_Call
             (Name   => New_Bool_Int_Cmp (Cmp),
              Args   => (1 => +Left, 2 => +Right),
              Domain => Domain);
      end if;
   end New_Comparison;

   -----------------
   -- New_Or_Expr --
   -----------------

   function New_Or_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id is
   begin
      if Is_False_Boolean (Left) then
         return Right;
      elsif Is_False_Boolean (Right) then
         return Left;
      else
         if Domain = EW_Pred then
            return New_Connection
              (Op     => EW_Or,
               Left   => +Left,
               Right  => +Right,
               Domain => Domain);
         else
            return New_Call
              (Domain => Domain,
               Name => New_Identifier ("bool_or"),
               Args => (1 => +Left, 2 => +Right));
         end if;
      end if;
   end New_Or_Expr;

   ----------------------
   -- New_Or_Else_Expr --
   ----------------------

   function New_Or_Else_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain) return W_Expr_Id
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
                (Op    => EW_Or_Else,
                 Left  => Left,
                 Right => Right);
         else
            return New_Or_Expr (Left, Right, Domain);
         end if;
      end if;
   end New_Or_Else_Expr;

   ----------------
   -- New_Result --
   ----------------

   function New_Result
     (T : W_Simple_Value_Type_Id)
     return W_Binder_Id is
   begin
      return New_Binder
        (Name     => New_Result_Identifier.Id,
         Arg_Type => T);
   end New_Result;

   ------------------------
   -- New_Simpl_Any_Expr --
   ------------------------

   function New_Simpl_Any_Expr (T : W_Primitive_Type_Id) return W_Prog_Id
   is
   begin
      return
         New_Any_Expr
            (Any_Type =>
               New_Computation_Type
                  (Result  => New_Result (+T),
                   Effects => New_Effects));
   end New_Simpl_Any_Expr;

   ---------------------------
   -- New_Simpl_Conditional --
   ---------------------------

   function New_Simpl_Conditional
      (Condition : W_Expr_Id;
       Then_Part : W_Expr_Id;
       Else_Part : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id
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
              Domain    => Domain);
      end if;
   end New_Simpl_Conditional;

   --------------
   -- New_Void --
   --------------

   function Sequence (Left, Right : W_Prog_Id) return W_Prog_Id
   is
      function Is_Void (N : W_Prog_Id) return Boolean;
      --  Detect if the node represents the Void Literal

      --------------
      -- Is_Void --
      --------------

      function Is_Void (N : W_Prog_Id) return Boolean
      is
      begin
         return Get_Kind (+N) = W_Void;
      end Is_Void;

      --  begin processing for Sequence
   begin
      --  We only optimize the case where at least one of (Left, Right) is not
      --  a sequence; in this case we append the not-sequence statement to the
      --  sequence statement.
      --  If both are sequences, or both are non-sequences, we use
      --  New_Statement_Sequence.
      if Is_Void (Left) then
         return Right;
      elsif Is_Void (Right) then
         return Left;
      end if;

      case Get_Kind (+Left) is
         when W_Statement_Sequence =>
            case Get_Kind (+Right) is
               when W_Statement_Sequence =>
                  return New_Statement_Sequence
                     (Statements => (1 => Left, 2 => Right));
               when others =>
                  Statement_Sequence_Append_To_Statements
                     (Id => W_Statement_Sequence_Id (Left), New_Item => Right);
                  return Left;
            end case;
         when others =>
            case Get_Kind (+Right) is
               when W_Statement_Sequence =>
                  Statement_Sequence_Prepend_To_Statements
                     (Id => W_Statement_Sequence_Id (Right), New_Item => Left);
                  return Right;
               when others =>
                  return New_Statement_Sequence
                     (Statements => (1 => Left, 2 => Right));
            end case;
      end case;
   end Sequence;

end Why.Gen.Progs;
