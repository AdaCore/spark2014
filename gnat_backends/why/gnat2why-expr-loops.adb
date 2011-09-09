------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - E X P R - L O O P                   --
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

with Gnat2Why.Driver;       use Gnat2Why.Driver;
with Nlists;                use Nlists;
with Uintp;                 use Uintp;
with VC_Kinds;              use VC_Kinds;
with Why;                   use Why;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Conversions;       use Why.Conversions;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Preds;         use Why.Gen.Preds;
with Why.Gen.Progs;         use Why.Gen.Progs;
with Why.Types;             use Why.Types;

package body Gnat2Why.Expr.Loops is

   procedure Compute_Invariant
      (Loop_Body  : List_Id;
       Pred       : out W_Pred_Id;
       Split_Node : out Node_Id);
   --  Given a list of statements (a loop body), construct a predicate that
   --  corresponds to the conjunction of all assertions at the beginning of
   --  the list. The out parameter Split_Node is set to the last node that is
   --  an assertion.
   --  If there are no assertions, we set Split_Node to N_Empty and we return
   --  True.

   function Wrap_Loop
      (Loop_Body : W_Prog_Id;
       Condition : W_Prog_Id;
       Loop_Name : String;
       Invariant : W_Pred_Id;
       Inv_Node  : Node_Id)
      return W_Prog_Id;
   --  Given a loop body and condition, generate the expression
   --  if <condition> then
   --    try
   --      loop {inv}
   --         <loop body>
   --         if not <condition> then raise <loop_name>;
   --      end loop
   --    with <loop_name> -> void
   --  end if

   -----------------------
   -- Compute_Invariant --
   -----------------------

   procedure Compute_Invariant
      (Loop_Body  : List_Id;
       Pred       : out W_Pred_Id;
       Split_Node : out Node_Id)
   is
      Cur_Stmt : Node_Id := Nlists.First (Loop_Body);
   begin
      Pred := New_Literal (Value => EW_True);
      Split_Node := Empty;

      while Nkind (Cur_Stmt) /= N_Empty loop
         case Nkind (Cur_Stmt) is
            when N_Pragma =>
               Pred :=
                 +New_And_Expr
                   (Left => +Pred,
                    Right => +Predicate_Of_Pragma_Check (Cur_Stmt),
                    Domain => EW_Pred);

            when others =>
               exit;
         end case;

         Split_Node := Cur_Stmt;
         Nlists.Next (Cur_Stmt);
      end loop;
   end Compute_Invariant;

   ------------------------------
   -- Transform_Loop_Statement --
   ------------------------------

   function Transform_Loop_Statement (Stmt : Node_Id) return W_Prog_Id
   is
      Loop_Body    : constant List_Id := Statements (Stmt);
      Split_Node   : Node_Id;
      Invariant    : W_Pred_Id;
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
      Compute_Invariant (Loop_Body, Invariant, Split_Node);
      Loop_Content :=
         Why_Expr_Of_Ada_Stmts
           (Stmts      => Loop_Body,
            Start_From => Split_Node);

      if Nkind (Scheme) = N_Empty then
         --  No iteration scheme, we have a simple loop. Generate
         --  condition "true".
         return
            Wrap_Loop
               (Loop_Body => Loop_Content,
                Condition => New_Literal (Value => EW_True),
                Loop_Name => Loop_Name,
                Invariant => Invariant,
                Inv_Node  => Split_Node);

      elsif
        Nkind (Iterator_Specification (Scheme)) = N_Empty
          and then
        Nkind (Loop_Parameter_Specification (Scheme)) = N_Empty
      then
         --  A while loop
         declare
            Enriched_Inv : constant W_Pred_Id :=
                             +New_And_Expr
                               (Left   => +Invariant,
                                Right  =>
                                  Transform_Expr
                                    (Condition (Scheme), EW_Pred),
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
                 +Transform_Expr (Condition (Scheme), EW_Prog),
               Loop_Name    => Loop_Name,
               Invariant    => Enriched_Inv,
               Inv_Node     => Inv_Node);
         end;

      elsif Nkind (Condition (Scheme)) = N_Empty then
         --  A for loop
         declare
            LParam_Spec  : constant Node_Id :=
                             Loop_Parameter_Specification (Scheme);
            Loop_Range   : constant Node_Id :=
                             Discrete_Subtype_Definition
                               (LParam_Spec);
            Loop_Index   : constant W_Identifier_Id :=
                             New_Identifier
                               (Full_Name
                                  (Defining_Identifier
                                    (LParam_Spec)));
            Index_Deref  : constant W_Prog_Id :=
                             New_Unary_Op
                               (Ada_Node => Stmt,
                                Domain   => EW_Prog,
                                Op       => EW_Deref,
                                Right    => +Loop_Index);
            Addition     : constant W_Prog_Id :=
                             New_Binary_Op
                               (Ada_Node => Stmt,
                                Domain   => EW_Prog,
                                Op       => EW_Add,
                                Op_Type  => EW_Int,
                                Left     => +Index_Deref,
                                Right    =>
                                  New_Integer_Constant
                                    (Ada_Node => Stmt,
                                     Value     => Uint_1));
            Incr_Stmt    : constant W_Prog_Id :=
                             New_Assignment
                               (Ada_Node => Stmt,
                                Name     => Loop_Index,
                                Value    => Addition);
            Enriched_Inv : constant W_Pred_Id :=
                             +New_And_Expr
                               (Left  => +Invariant,
                                Right =>
                                  Range_Expr
                                   (Loop_Range,
                                    New_Unary_Op
                                      (Domain   => EW_Term,
                                      Op       => EW_Deref,
                                      Right    => +Loop_Index),
                                    EW_Pred),
                                Domain => EW_Pred);
            --  We have enriched the invariant, so even if there was
            --  none at the beginning, we need to put a location here.
            Inv_Node     : constant Node_Id :=
                             (if Present (Split_Node) then Split_Node
                              else Stmt);
            Entire_Loop  : constant W_Prog_Id :=
                             Wrap_Loop
                               (Loop_Body    =>
                                  Sequence (Loop_Content, Incr_Stmt),
                                Condition    =>
                                  +Range_Expr
                                    (Loop_Range,
                                     +Index_Deref,
                                     EW_Prog),
                                Loop_Name    => Loop_Name,
                                Invariant    => Enriched_Inv,
                                Inv_Node     => Inv_Node);
            Low          : constant Node_Id :=
                             Low_Bound
                               (Get_Range
                                 (Discrete_Subtype_Definition
                                   (LParam_Spec)));
         begin
            return
              New_Binding_Ref
                (Name    => Loop_Index,
                 Def     => +Transform_Expr (Low,
                                                   EW_Int_Type,
                                                   EW_Prog),
                 Context => Entire_Loop);
         end;

      else
         --  Some other kind of loop
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
       Inv_Node  : Node_Id)
      return W_Prog_Id
   is
      Entire_Body : constant W_Prog_Id :=
                      Sequence
                        (Loop_Body,
                         New_Conditional
                           (Domain    => EW_Prog,
                            Condition =>
                              New_Not (Right => +Condition, Domain => EW_Prog),
                            Then_Part =>
                              New_Raise
                                (Name => New_Identifier (Loop_Name))));
      Loop_Stmt   : constant W_Prog_Id :=
                      New_While_Loop
                        (Condition   => New_Literal (Value => EW_True),
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
        (Current_Why_Output_File,
         New_Exception_Declaration
           (Name => New_Identifier (Loop_Name),
            Arg  => Why.Types.Why_Empty));

      return
        New_Conditional
          (Domain    => EW_Prog,
           Condition => Condition,
           Then_Part =>
             New_Try_Block
               (Prog    => Loop_Stmt,
                Handler =>
                  (1 =>
                     New_Handler
                       (Name => New_Identifier (Loop_Name),
                        Def  => New_Void))));
   end Wrap_Loop;
end Gnat2Why.Expr.Loops;
