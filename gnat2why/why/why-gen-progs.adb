------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R O G S                         --
--                                                                          --
--                                 B o d y                                  --
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

with Uintp;                use Uintp;

with Why.Conversions;      use Why.Conversions;
with Why.Atree.Mutators;   use Why.Atree.Mutators;
with Why.Atree.Properties; use Why.Atree.Properties;
with Why.Atree.Tables;     use Why.Atree.Tables;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Expr;         use Why.Gen.Expr;
with Why.Inter;            use Why.Inter;

package body Why.Gen.Progs is

   --------------------------
   -- New_Assume_Statement --
   --------------------------

   function New_Assume_Statement
     (Ada_Node    : Node_Id := Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id;
      Return_Type : W_Primitive_Type_Id := Why_Empty)
      return W_Prog_Id is
   begin
      return
        New_Any_Expr
          (Ada_Node => Ada_Node,
           Pre      => Pre,
           Post     => Post,
           Return_Type =>
             +(if Return_Type = Why_Empty then +EW_Unit_Type
               else Return_Type));
   end New_Assume_Statement;

   ------------------
   -- New_For_Loop --
   ------------------

   function New_For_Loop
     (Ada_Node   : Node_Id;
      Loop_Index : W_Identifier_Id;
      Low        : W_Identifier_Id;
      High       : W_Identifier_Id;
      Invariant  : W_Pred_Id;
      Loop_Body  : W_Prog_Id) return W_Prog_Id
   is
      Index_Deref  : constant W_Prog_Id :=
                       New_Deref
                         (Ada_Node => Ada_Node,
                          Right    => Loop_Index);
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
                          Op_Type  => EW_Int,
                          Op       => EW_Le,
                          Left     => +Index_Deref,
                          Right    => +High);
      Loop_Content : constant W_Prog_Id :=
                       New_Statement_Sequence
                         (Ada_Node   => Ada_Node,
                          Statements => (1 => Loop_Body, 2 => Incr_Stmt));
      Enriched_Inv : constant W_Pred_Id :=
                       New_Connection
                         (Op     => EW_Or,
                          Left   => +Invariant,
                          Right  =>
                            New_Relation
                              (Domain  => EW_Pred,
                               Op_Type => EW_Int,
                               Left    => +Low,
                               Op      => EW_Le,
                               Right   => +Loop_Index,
                               Op2     => EW_Le,
                               Right2  =>
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
                        +New_VC_Expr
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
      Call : constant W_Prog_Id :=
        New_Call
          (Ada_Node => Ada_Node,
           Name     => To_Ident (WNE_Ignore),
           Args     => (1 => +Prog));
   begin
      return New_Abstract_Expr (Expr => Call, Post => True_Pred);
   end New_Ignore;

   --------------------------
   -- New_Located_Abstract --
   --------------------------

   function New_Located_Abstract
     (Ada_Node  : Node_Id;
      Expr : W_Prog_Id;
      Post : W_Pred_Id) return W_Prog_Id
   is
   begin
      return
        New_Abstract_Expr
          (Ada_Node => Ada_Node,
           Expr     => Expr,
           Post     =>
           +New_VC_Expr
             (Ada_Node => Ada_Node,
              Expr     => +Post,
              Reason   => VC_Assert,
              Domain   => EW_Pred));
   end New_Located_Abstract;

   ------------------------
   -- New_Located_Assert --
   ------------------------

   function New_Located_Assert
      (Ada_Node : Node_Id;
       Pred     : W_Pred_Id;
       Reason   : VC_Kind) return W_Prog_Id
   is
      (New_Assert (Ada_Node => Ada_Node,
                   Pred     => +New_VC_Expr (Ada_Node => Ada_Node,
                                             Expr     => +Pred,
                                             Reason   => Reason,
                                             Domain   => EW_Pred)));

   function New_Located_Assert
      (Ada_Node : Node_Id;
       Pred     : W_Pred_Id) return W_Prog_Id
   is
      (New_Located_Assert (Ada_Node, Pred, VC_Assert));

   ----------------
   -- New_Result --
   ----------------

   function New_Result
     (T : W_Primitive_Type_Id)
     return W_Binder_Id is
   begin
      return New_Binder
        (Domain   => EW_Term,
         Name     => To_Ident (WNE_Result),
         Arg_Type => T);
   end New_Result;

   ------------------------
   -- New_Simpl_Any_Prog --
   ------------------------

   function New_Simpl_Any_Prog
     (T    : W_Primitive_Type_Id;
      Pred : W_Pred_OId := Why_Empty) return W_Prog_Id
   is
   begin
      return
        New_Any_Expr
          (Post        => Pred,
           Return_Type => +T);
   end New_Simpl_Any_Prog;

   --------------
   -- Sequence --
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
                  if Is_Root (+Left) then
                     Statement_Sequence_Append_To_Statements
                        (Id => W_Statement_Sequence_Id (Left),
                         New_Item => Right);
                     return Left;
                  else
                     return New_Statement_Sequence
                        (Statements => (1 => Left, 2 => Right));
                  end if;
            end case;
         when others =>
            case Get_Kind (+Right) is
               when W_Statement_Sequence =>
                  if Is_Root (+Right) then
                     Statement_Sequence_Prepend_To_Statements
                        (Id => W_Statement_Sequence_Id (Right),
                         New_Item => Left);
                     return Right;
                  else
                     return New_Statement_Sequence
                        (Statements => (1 => Left, 2 => Right));
                  end if;
               when others =>
                  return New_Statement_Sequence
                     (Statements => (1 => Left, 2 => Right));
            end case;
      end case;
   end Sequence;

   function Sequence (Progs : W_Prog_Array) return W_Prog_Id is
      Result : W_Prog_Id := Progs (Progs'First);
   begin
      for J in Progs'First + 1 .. Progs'Last loop
         Result := Sequence (Result, Progs (J));
      end loop;
      return Result;
   end Sequence;

end Why.Gen.Progs;
