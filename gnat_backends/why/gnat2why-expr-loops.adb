------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - E X P R - L O O P                   --
--                                                                          --
--                                 B o d y                                  --
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

--  For debugging, to print info on the output before raising an exception
with Ada.Text_IO;

with Gnat2Why.Driver;       use Gnat2Why.Driver;
with Nlists;                use Nlists;
with Snames;                use Snames;
with Uintp;                 use Uintp;
with VC_Kinds;              use VC_Kinds;
with Why;                   use Why;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Conversions;       use Why.Conversions;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Expr;          use Why.Gen.Expr;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Progs;         use Why.Gen.Progs;
with Why.Gen.Preds;         use Why.Gen.Preds;
with Why.Types;             use Why.Types;
with Why.Inter;             use Why.Inter;

package body Gnat2Why.Expr.Loops is

   procedure Compute_Invariant
      (Loop_Body  : List_Id;
       Pred       : out W_Pred_Id;
       Inv_Check  : out W_Prog_Id;
       Split_Node : out Node_Id);
   --  Given a list of statements (a loop body), construct a predicate that
   --  corresponds to the conjunction of all assertions at the beginning of
   --  the list. The out parameter Split_Node is set to the last node that is
   --  an assertion.
   --  If there are no assertions, we set Split_Node to N_Empty and we return
   --  True.
   --  The out parameter Inv_Check contains an expression that corresponds to
   --  the runtime checks of the invariant.

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id;
   --  Return the Defining_Identifier of the loop that belongs to an exit
   --  statement.

   function Wrap_Loop
      (Loop_Body : W_Prog_Id;
       Condition : W_Prog_Id;
       Loop_Name : String;
       Invariant : W_Pred_Id;
       Inv_Check : W_Prog_Id;
       Inv_Node  : Node_Id)
      return W_Prog_Id;
   --  Given a loop body, the loop condition, the loop name, the invariant,
   --  the check_expression for the invariant, generate the entire loop
   --  expression in Why.
   --  See the comment in the body of Wrap_Loop to see how it's done.

   -----------------------
   -- Compute_Invariant --
   -----------------------

   procedure Compute_Invariant
      (Loop_Body  : List_Id;
       Pred       : out W_Pred_Id;
       Inv_Check  : out W_Prog_Id;
       Split_Node : out Node_Id)
   is
      Cur_Stmt : Node_Id := Nlists.First (Loop_Body);
   begin
      Pred := True_Pred;
      Inv_Check := New_Void;
      Split_Node := Empty;

      while Nkind (Cur_Stmt) /= N_Empty loop
         case Nkind (Cur_Stmt) is
            when N_Pragma =>
               if Get_Pragma_Id (Pragma_Name (Cur_Stmt)) = Pragma_Check then
                  declare
                     Cur_Check : W_Prog_Id;
                     Cur_Pred : constant W_Pred_Id :=
                        Transform_Pragma_Check (Cur_Stmt, Cur_Check);
                  begin
                     Pred := +New_And_Expr (+Pred, +Cur_Pred, EW_Pred);
                     Inv_Check := Sequence (Inv_Check, Cur_Check);
                  end;
               end if;

            when N_Object_Declaration =>
               null;

            when others =>
               exit;
         end case;

         Split_Node := Cur_Stmt;
         Nlists.Next (Cur_Stmt);
      end loop;
   end Compute_Invariant;

   -----------------------------------
   -- Loop_Entity_Of_Exit_Statement --
   -----------------------------------

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id is
   begin
      --  If the name is directly in the given node, return that name

      if Present (Name (N)) then
         return Entity (Name (N));

      --  Otherwise the exit statement belongs to the innermost loop, so
      --  simply go upwards (follow parent nodes) until we encounter the
      --  loop

      else
         declare
            Cur_Node : Node_Id := N;
         begin
            while Nkind (Cur_Node) /= N_Loop_Statement loop
               Cur_Node := Parent (Cur_Node);
            end loop;
            return Entity (Identifier (Cur_Node));
         end;
      end if;
   end Loop_Entity_Of_Exit_Statement;

   ------------------------------
   -- Transform_Exit_Statement --
   ------------------------------

   function Transform_Exit_Statement (Stmt : Node_Id) return W_Prog_Id
   is
      Loop_Entity : constant Entity_Id := Loop_Entity_Of_Exit_Statement (Stmt);
      Exc_Name    : constant String := Full_Name (Loop_Entity);
      Raise_Stmt  : constant W_Prog_Id :=
                      New_Raise
                        (Ada_Node => Stmt,
                         Name => New_Identifier (Name => Exc_Name));
   begin
      if Nkind (Condition (Stmt)) = N_Empty then
         return Raise_Stmt;
      else
         return
           New_Conditional
             (Ada_Node  => Stmt,
              Condition => +Transform_Expr (Condition (Stmt),
                                            EW_Bool_Type,
                                            EW_Prog,
                                            Params => Body_Params),
              Then_Part => +Raise_Stmt);
      end if;
   end Transform_Exit_Statement;

   ------------------------------
   -- Transform_Loop_Statement --
   ------------------------------

   function Transform_Loop_Statement (Stmt : Node_Id) return W_Prog_Id
   is
      Loop_Body    : constant List_Id := Statements (Stmt);
      Split_Node   : Node_Id;
      Invariant    : W_Pred_Id;
      Inv_Check    : W_Prog_Id;
      Loop_Content : W_Prog_Id;
      Scheme       : constant Node_Id := Iteration_Scheme (Stmt);
      Loop_Entity  : constant Entity_Id := Entity (Identifier (Stmt));
      Loop_Name    : constant String := Full_Name (Loop_Entity);
   begin
      --  We have to take into consideration
      --    * We simulate loop *assertions* by Hoare loop *invariants*;
      --      A Hoare invariant must be initially true whether we enter
      --      the loop or not; it must also be true at the exit of the
      --      loop.
      --      This means that we have to protect the loop to avoid
      --      encountering it if the condition is false; also we exit
      --      the loop at the end (instead of the beginning) when the
      --      condition becomes false:
      --      if cond then
      --          loop
      --             <loop body>
      --             exit when not cond
      --          end loop
      --       end if
      --    * We need to model exit statements; we use Why exceptions
      --      for this:
      --       (at toplevel)
      --         exception Loop_Name
      --       (in statement sequence)
      --         try
      --           loop
      --             <loop_body>
      --           done
      --         with Loop_Name -> void
      --
      --     The exception is necessary to deal with N_Exit_Statements
      --     (see also the corresponding case). The exception has to be
      --     declared at the toplevel.
      Compute_Invariant (Loop_Body, Invariant, Inv_Check, Split_Node);
      Loop_Content :=
         Transform_Statements
           (Stmts      => Loop_Body,
            Start_From => Split_Node);

      --  No iteration scheme, we have a simple loop. Generate condition
      --  "true".

      if Nkind (Scheme) = N_Empty then
         return
            Wrap_Loop
               (Loop_Body => Loop_Content,
                Condition => True_Prog,
                Loop_Name => Loop_Name,
                Invariant => Invariant,
                Inv_Check => Inv_Check,
                Inv_Node  => Split_Node);

      --  A while loop

      elsif
        Nkind (Iterator_Specification (Scheme)) = N_Empty
          and then
        Nkind (Loop_Parameter_Specification (Scheme)) = N_Empty
      then
         While_Loop : declare
            Enriched_Inv : constant W_Pred_Id :=
                             +New_And_Expr
                               (Left   => +Invariant,
                                Right  =>
                                  Transform_Expr_With_Actions
                                    (Condition (Scheme),
                                     Condition_Actions (Scheme),
                                     EW_Pred,
                                     Params => Body_Params),
                                Domain => EW_Pred);
            --  We have enriched the invariant, so even if there was
            --  none at the beginning, we need to put a location here.
            Inv_Node : constant Node_Id :=
                         (if Present (Split_Node) then Split_Node
                          else Stmt);
         begin
            return
              Wrap_Loop
              (Loop_Body    => Loop_Content,
               Condition    =>
                 +Transform_Expr_With_Actions (Condition (Scheme),
                                               Condition_Actions (Scheme),
                                               EW_Bool_Type,
                                               EW_Prog,
                                               Params => Body_Params),
               Loop_Name    => Loop_Name,
               Invariant    => Enriched_Inv,
               Inv_Check    => Inv_Check,
               Inv_Node     => Inv_Node);
         end While_Loop;

      --  A for loop. Here, we set the condition to express that the index is
      --  in the range of the loop. We need to evaluate the range expression
      --  once at the beginning of the loop, to get potential checks in that
      --  expression only once.

      elsif Nkind (Condition (Scheme)) = N_Empty then
         Plain_Loop : declare
            LParam_Spec  : constant Node_Id :=
                             Loop_Parameter_Specification (Scheme);
            Loop_Range   : constant Node_Id :=
              Discrete_Subtype_Definition (LParam_Spec);
            Ent          : constant Entity_Id :=
              Defining_Identifier (LParam_Spec);
            Loop_Index   : constant W_Identifier_Id :=
              New_Identifier
                (Ada_Node => Etype (Ent),
                 Name => Full_Name (Ent));
            Index_Deref  : constant W_Prog_Id :=
                             New_Deref
                               (Ada_Node => Stmt,
                                Right    => +Loop_Index);
            Update_Op    : constant EW_Binary_Op :=
                             (if Reverse_Present (LParam_Spec) then
                                EW_Substract
                              else
                                EW_Add);
            Update_Expr  : constant W_Prog_Id :=
                             New_Binary_Op
                               (Ada_Node => Stmt,
                                Op       => Update_Op,
                                Op_Type  => EW_Int,
                                Left     => +Index_Deref,
                                Right    =>
                                  New_Integer_Constant
                                    (Ada_Node => Stmt,
                                     Value     => Uint_1));
            Update_Stmt  : constant W_Prog_Id :=
                             New_Assignment
                               (Ada_Node => Stmt,
                                Name     => Loop_Index,
                                Value    => Update_Expr);

            --  In the range expression of the invariant, explicitly
            --  set T_Type to handle the special case of
            --  Standard.Boolean, where bounds and index are of
            --  different base types (bool for bounds, int for index).

            Enriched_Inv : constant W_Pred_Id :=
                             +New_And_Expr
                               (Left  => +Invariant,
                                Right =>
                                  Range_Expr
                                   (Loop_Range,
                                    New_Deref (Right => Loop_Index),
                                    EW_Pred,
                                    Params => Body_Params,
                                    T_Type      => EW_Int_Type),
                                Domain => EW_Pred);
            --  We have enriched the invariant, so even if there was
            --  none at the beginning, we need to put a location here.
            Inv_Node     : constant Node_Id :=
                             (if Present (Split_Node) then Split_Node
                              else Stmt);
            Actual_Range : constant Node_Id := Get_Range (Loop_Range);
            Low_Ident    : constant W_Identifier_Id := New_Temp_Identifier;
            High_Ident   : constant W_Identifier_Id := New_Temp_Identifier;
            Condition    : constant W_Prog_Id :=
                             +New_Range_Expr
                               (Domain    => EW_Prog,
                                Base_Type => EW_Int_Type,
                                Low       => +Low_Ident,
                                High      => +High_Ident,
                                Expr      => +Index_Deref);
            Entire_Loop  : W_Prog_Id :=
                             Wrap_Loop
                               (Loop_Body    =>
                                  Sequence (Loop_Content, Update_Stmt),
                                Condition    => Condition,
                                Loop_Name    => Loop_Name,
                                Invariant    => Enriched_Inv,
                                Inv_Check    => Inv_Check,
                                Inv_Node     => Inv_Node);
            Init_Index  : constant W_Identifier_Id :=
                            (if Reverse_Present (LParam_Spec) then
                               High_Ident
                             else
                               Low_Ident);

         --  Start of Plain_Loop

         begin
            Entire_Loop := New_Binding_Ref
                             (Name    => Loop_Index,
                              Def     => +Init_Index,
                              Context => Entire_Loop);
            Entire_Loop :=
               New_Binding
                 (Name    => High_Ident,
                  Def     => +Transform_Expr (High_Bound (Actual_Range),
                                              EW_Int_Type,
                                              EW_Prog,
                                              Params => Body_Params),
                  Context => +Entire_Loop);
            Entire_Loop :=
               New_Binding
                 (Name    => Low_Ident,
                  Def     => +Transform_Expr (Low_Bound (Actual_Range),
                                              EW_Int_Type,
                                              EW_Prog,
                                              Params => Body_Params),
                  Context => +Entire_Loop);
            return
              Sequence
                (Assume_Of_Subtype_Indication (Body_Params, Loop_Range),
                 Entire_Loop);
         end Plain_Loop;

      else
         --  Some other kind of loop
         Ada.Text_IO.Put_Line ("[Transform_Loop_Statement] other loop");
         raise Not_Implemented;
      end if;
   end Transform_Loop_Statement;

   ---------------
   -- Wrap_Loop --
   ---------------

   function Wrap_Loop
      (Loop_Body : W_Prog_Id;
       Condition : W_Prog_Id;
       Loop_Name : String;
       Invariant : W_Pred_Id;
       Inv_Check : W_Prog_Id;
       Inv_Node  : Node_Id)
      return W_Prog_Id
   is

      --  Given a loop body and condition, generate the expression
      --  if <condition> then
      --    ignore (inv);
      --    try
      --      loop {inv}
      --         <loop body>
      --         if <condition> then ignore (inv)
      --         else raise <loop_name>;
      --      end loop
      --    with <loop_name> -> void
      --  end if

      Entire_Body : constant W_Prog_Id :=
                      Sequence
                        (Loop_Body,
                         New_Conditional
                           (Condition => +Condition,
                            Then_Part => +Inv_Check,
                            Else_Part =>
                              New_Raise
                                (Name => New_Identifier (Name => Loop_Name))));
      Loop_Stmt   : constant W_Prog_Id :=
                      New_While_Loop
                        (Condition   => True_Prog,
                         Annotation  =>
                           New_Loop_Annot
                             (Invariant =>
                                +New_Located_Expr
                                  (Ada_Node => Inv_Node,
                                   Expr     => +Invariant,
                                   Reason   => VC_Loop_Invariant,
                                   Domain   => EW_Pred)),
                         Loop_Content => Entire_Body);
   begin
      Emit
        (Body_Params.Theory,
         New_Exception_Declaration
           (Name => New_Identifier (Name => Loop_Name),
            Arg  => Why.Types.Why_Empty));

      return
        New_Conditional
          (Condition => +Condition,
           Then_Part =>
             +Sequence
               (Inv_Check,
                New_Try_Block
                  (Prog    => Loop_Stmt,
                   Handler =>
                     (1 =>
                        New_Handler
                          (Name => New_Identifier (Name => Loop_Name),
                           Def  => New_Void)))));
   end Wrap_Loop;

end Gnat2Why.Expr.Loops;
