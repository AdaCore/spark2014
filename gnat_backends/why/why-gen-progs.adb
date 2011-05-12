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

with Uintp;               use Uintp;

with Gnat2Why.Decls;      use Gnat2Why.Decls;
with Gnat2Why.Locs;       use Gnat2Why.Locs;

with Why.Conversions;     use Why.Conversions;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Preds;       use Why.Gen.Preds;

package body Why.Gen.Progs is

   function Convert_From_Int
      (Ada_Node : Node_Id := Empty;
       To       : Why_Type;
       Why_Expr : W_Prog_Id;
       Reason   : VC_Kind := VC_Range_Check) return W_Prog_Id;
   --  Convert the Why expression in argument to "int". It is expected to be
   --  of type "From".

   function Convert_To_Int
      (Ada_Node : Node_Id := Empty;
       From     : Why_Type;
       Why_Expr : W_Prog_Id) return W_Prog_Id;
   --  Convert the Why expression in argument to "int". It is expected to be
   --  of type "From".

   function Is_False_Boolean (P : W_Prog_Id) return Boolean;
   --  Check if the given program is the program "false"

   function Is_True_Boolean (P : W_Prog_Id) return Boolean;
   --  Check if the given program is the program "true"

   function New_Located_Prog
      (Ada_Node : Node_Id;
       Prog     : W_Prog_Id;
       Reason   : VC_Kind) return W_Prog_Id;
   --  Build a program with a fresh label corresponding to the Ada_Node.

   ---------------------
   -- Conversion_Name --
   ---------------------

   function Conversion_Name
      (From : Why_Type;
       To   : Why_Type) return W_Identifier_Id
   is
   begin
      case From.Kind is
         when Why_Int =>
            case To.Kind is
               when Why_Int =>
                  --  We have assumed the two arguments to be different
                  raise Program_Error;
               when Why_Abstract =>
                  return
                     New_Conversion_From_Int
                       (Full_Name (To.Wh_Abstract));
            end case;
         when Why_Abstract =>
            case To.Kind is
               when Why_Int =>
                  return
                    New_Conversion_To_Int (Full_Name (From.Wh_Abstract));
               when Why_Abstract =>
                  raise Program_Error
                     with "Conversion between arbitrary types attempted";
            end case;
      end case;
   end Conversion_Name;

   --------------------
   -- Convert_To_Int --
   --------------------

   function Convert_To_Int
      (Ada_Node : Node_Id := Empty;
       From     : Why_Type;
       Why_Expr : W_Prog_Id) return W_Prog_Id
   is
   begin
      return
        New_Prog_Call
          (Ada_Node => Ada_Node,
           Name     => Conversion_Name (From => From, To => (Kind => Why_Int)),
           Progs    => (1 => Why_Expr));
   end Convert_To_Int;

   ----------------------
   -- Convert_From_Int --
   ----------------------

   function Convert_From_Int
      (Ada_Node : Node_Id := Empty;
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
              (Conversion_Name (From => (Kind => Why_Int), To => To)),
           Progs    => (1 => Why_Expr),
           Reason   => Reason);
   end Convert_From_Int;

   -----------------------
   -- Insert_Conversion --
   -----------------------

   function Insert_Conversion
      (Ada_Node : Node_Id := Empty;
       To                    : Why_Type;
       From                  : Why_Type;
       Why_Expr              : W_Prog_Id;
       Base_Type              : Why_Type := (Kind => Why_Int)) return W_Prog_Id
   is
   begin
      if Base_Type.Kind = Why_Int and then To = From then
         return Why_Expr;
      end if;

      if To.Kind = Why_Int then
         --  We convert to "int"
         if not (Base_Type.Kind = Why_Int) and then From.Kind = Why_Int then
            --  If both types are "int", and we have a Base_Type, insert a
            --  conversion
            return
               Convert_To_Int
                 (Ada_Node => Ada_Node,
                  From     => Base_Type,
                  Why_Expr =>
                     Convert_From_Int
                        (Ada_Node => Ada_Node,
                         To       => Base_Type,
                         Why_Expr => Why_Expr,
                         Reason   => VC_Overflow_Check));
         else
            return Convert_To_Int (Ada_Node, From, Why_Expr);
         end if;

      elsif From.Kind = Why_Int then
         return Convert_From_Int (Ada_Node, To, Why_Expr);
      else
         return
            Insert_Conversion
               (Ada_Node => Ada_Node,
                To       => To,
                From     => (Kind => Why_Int),
                Why_Expr =>
                  Insert_Conversion
                    (Ada_Node => Ada_Node,
                     To       => (Kind => Why_Int),
                     From     => From,
                     Why_Expr => Why_Expr));
      end if;
   end Insert_Conversion;

   ----------------------
   -- Is_False_Boolean --
   ----------------------

   function Is_False_Boolean (P : W_Prog_Id) return Boolean
   is
   begin
      return
         (Get_Kind (+P) = W_Prog_Constant and then
          Get_Kind (Prog_Constant_Get_Def (+P)) = W_False_Literal);
   end Is_False_Boolean;

   ---------------------
   -- Is_True_Boolean --
   ---------------------

   function Is_True_Boolean (P : W_Prog_Id) return Boolean
   is
   begin
      return
         (Get_Kind (+P) = W_Prog_Constant and then
          Get_Kind (Prog_Constant_Get_Def (+P)) = W_True_Literal);
   end Is_True_Boolean;

   --------------------------
   -- New_Assume_Statement --
   --------------------------

   function New_Assume_Statement
      (Ada_Node    : Node_Id;
       Pred        : W_Predicate_Id;
       Return_Type : W_Primitive_Type_Id := New_Type_Unit)
       return W_Prog_Id
   is
   begin
      return
         New_Any_Expr
            (Ada_Node => Ada_Node,
             Any_Type =>
               New_Computation_Type
                 (Ada_Node => Ada_Node,
                  Return_Type => Return_Type,
                  Effects => New_Effects,
                  Postcondition =>
                     New_Postcondition (Ada_Node => Ada_Node, Pred => Pred)));
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
      Index_Deref : constant W_Prog_Id :=
         New_Deref
           (Ada_Node => Ada_Node,
            Ref      => Loop_Index);
      Addition : constant W_Prog_Id :=
         New_Infix_Call
            (Ada_Node => Ada_Node,
             Infix    => New_Op_Add_Prog,
             Left     => Index_Deref,
             Right    =>
               New_Prog_Constant
                 (Ada_Node => Ada_Node,
                  Def      =>
                    New_Integer_Constant
                      (Ada_Node => Ada_Node,
                      Value     => Uint_1)));
      Incr_Stmt : constant W_Prog_Id :=
         New_Assignment
            (Ada_Node => Ada_Node,
             Name     => +Duplicate_Any_Node (Id => +Loop_Index),
             Value    => Addition);
      Loop_Cond : constant W_Prog_Id  :=
         New_Infix_Call
           (Ada_Node => Ada_Node,
            Infix    => New_Op_Le_Prog,
            Left     =>
              +Duplicate_Any_Node (Id => +Index_Deref),
            Right    => New_Prog_Identifier (Def => High));
      Loop_Content : constant W_Prog_Id :=
         New_Statement_Sequence
            (Ada_Node   => Ada_Node,
             Statements => (1 => Loop_Body, 2 => Incr_Stmt));
      Enriched_Inv : constant W_Predicate_Id :=
         New_Conjunction
            (Left => Invariant,
             Right =>
               New_Related_Terms
                 (Left   => New_Term_Identifier (Name => Low),
                  Op     => New_Rel_Le,
                  Right  =>
                    New_Term_Identifier
                      (Name => +Duplicate_Any_Node (Id => +Loop_Index)),
                  Op2    => New_Rel_Le,
                  Right2 =>
                     New_Arith_Operation
                        (Op => New_Op_Add,
                         Left =>
                           New_Term_Identifier
                              (Name => +Duplicate_Any_Node (Id => +High)),
                         Right =>
                           New_Integer_Constant (Value => Uint_1))));
   begin
      return
        New_Binding_Ref
           (Ada_Node => Ada_Node,
            Name     => +Duplicate_Any_Node (Id => +Loop_Index),
            Def      =>
               New_Prog_Identifier (Def => +Duplicate_Any_Node (Id => +Low)),
            Context  =>
              New_While_Loop
                (Ada_Node     => Ada_Node,
                 Condition    => Loop_Cond,
                 Annotation   =>
                   New_Loop_Annot
                      (Invariant =>
                        New_Located_Predicate
                           (Ada_Node => Ada_Node,
                            Pred     => Enriched_Inv,
                            Reason   => VC_Loop_Invariant)),
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
         New_Prog_Call
           (Ada_Node => Ada_Node,
            Name     => New_Ignore_Name,
            Progs    => (1 => Prog));
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
           (Ada_Node   => Ada_Node,
            Preds =>
              (1 =>
                New_Located_Predicate
                  (Ada_Node => Ada_Node,
                   Pred     => Pred,
                   Reason   => VC_Assert)),
            Prog       => New_Void (Ada_Node));
   end New_Located_Assert;

   ----------------------
   -- New_Located_Call --
   ----------------------

   function New_Located_Call
      (Ada_Node : Node_Id;
       Name     : W_Identifier_Id;
       Progs    : W_Prog_Array;
       Reason   : VC_Kind) return W_Prog_Id
   is
   begin
      return
        New_Located_Prog
          (Ada_Node => Ada_Node,
           Reason   => Reason,
           Prog =>
             New_Prog_Call
               (Ada_Node => Ada_Node,
                Name => Name,
                Progs => Progs));
   end New_Located_Call;

   ----------------------
   -- New_Located_Prog --
   ----------------------

   function New_Located_Prog
      (Ada_Node : Node_Id;
       Prog     : W_Prog_Id;
       Reason   : VC_Kind) return W_Prog_Id
   is
   begin
      return
        New_Label
          (Ada_Node => Ada_Node,
           Name     => New_Located_Label (Ada_Node, Reason),
           Def      => Prog);
   end New_Located_Prog;

   -------------------
   -- New_Prog_Andb --
   -------------------

   function New_Prog_Andb (Left, Right : W_Prog_Id) return W_Prog_Id
   is
   begin
      if Is_True_Boolean (Left) then
         return Right;
      elsif Is_True_Boolean (Right) then
         return Left;
      else
         return
            New_Prog_Call
               (Name => New_Identifier ("bool_and"),
                Progs => (1 => Left, 2 => Right));
      end if;
   end New_Prog_Andb;

   ------------------------
   -- New_Prog_Andb_Then --
   ------------------------

   function New_Prog_Andb_Then (Left, Right : W_Prog_Id) return W_Prog_Id
   is
   begin
      if Is_True_Boolean (Left) then
         return Right;
      elsif Is_True_Boolean (Right) then
         return Left;
      else
         return
            New_Infix_Call
              (Infix    => New_Op_And_Then_Prog,
               Left     => Left,
               Right    => Right);
      end if;
   end New_Prog_Andb_Then;

   --------------------------
   -- New_Prog_Boolean_Cmp --
   --------------------------

   function New_Prog_Boolean_Cmp (Cmp : W_Relation; Left, Right : W_Prog_Id)
      return W_Prog_Id
   is
   begin
      return
         New_Prog_Call
           (Name => New_Bool_Int_Cmp (Cmp),
            Progs => (1 => Left, 2 => Right));

   end New_Prog_Boolean_Cmp;

   -------------------
   -- New_Prog_Notb --
   -------------------

   function New_Prog_Notb (Left : W_Prog_Id) return W_Prog_Id
   is
   begin
      return
        New_Prefix_Call
          (Prefix   => New_Op_Not_Prog,
           Operand  => Left);
   end New_Prog_Notb;

   ------------------
   -- New_Prog_Orb --
   ------------------

   function New_Prog_Orb (Left, Right : W_Prog_Id) return W_Prog_Id
   is
   begin
      if Is_False_Boolean (Left) then
         return Right;
      elsif Is_False_Boolean (Right) then
         return Left;
      else
         return
            New_Prog_Call
               (Name => New_Identifier ("bool_or"),
                Progs => (1 => Left, 2 => Right));
      end if;
   end New_Prog_Orb;

   -----------------------
   -- New_Prog_Orb_Else --
   -----------------------

   function New_Prog_Orb_Else (Left, Right : W_Prog_Id) return W_Prog_Id
   is
   begin
      if Is_False_Boolean (Left) then
         return Right;
      elsif Is_False_Boolean (Right) then
         return Left;
      else
         return
            New_Infix_Call
              (Infix    => New_Op_Or_Else_Prog,
               Left     => Left,
               Right    => Right);
      end if;
   end New_Prog_Orb_Else;

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
                  (Return_Type => T,
                   Effects     => New_Effects));
   end New_Simpl_Any_Expr;

   --------------------------------
   -- New_Simpl_Conditional_Prog --
   --------------------------------

   function New_Simpl_Conditional_Prog
      (Condition : W_Prog_Id;
       Then_Part : W_Prog_Id;
       Else_Part : W_Prog_Id) return W_Prog_Id
   is
   begin
      if Is_True_Boolean (Condition) then
         return Then_Part;
      elsif Is_False_Boolean (Condition) then
         return Else_Part;
      else
         return
            New_Conditional_Prog
               (Condition => Condition,
                Then_Part => Then_Part,
                Else_Part => Else_Part);
      end if;
   end New_Simpl_Conditional_Prog;

   ---------------------------
   -- New_True_Literal_Prog --
   ---------------------------

   function New_True_Literal_Prog (Ada_Node : Node_Id := Empty)
      return W_Prog_Id
   is
   begin
      return
        New_Prog_Constant
          (Ada_Node => Ada_Node,
           Def => New_True_Literal);
   end New_True_Literal_Prog;

   --------------
   -- New_Void --
   --------------

   function New_Void (Ada_Node : Node_Id := Empty) return W_Prog_Id
   is
   begin
      return New_Prog_Constant (Ada_Node => Ada_Node, Def => New_Void_Literal);
   end New_Void;

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
         return
           (Get_Kind (+N) = W_Prog_Constant and then
            Get_Kind (Prog_Constant_Get_Def (+N)) = W_Void_Literal);
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
