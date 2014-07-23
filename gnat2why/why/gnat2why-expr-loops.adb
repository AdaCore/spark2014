------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - E X P R - L O O P                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

with Atree;              use Atree;
with Namet;              use Namet;
with Nlists;             use Nlists;
with Sinfo;              use Sinfo;
with Snames;             use Snames;
with Uintp;              use Uintp;
with VC_Kinds;           use VC_Kinds;

with SPARK_Util;         use SPARK_Util;
with Flow_Types;
with Flow_Utility;       use Flow_Utility;

with Why;                use Why;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Modules;  use Why.Atree.Modules;
with Why.Atree.Tables;   use Why.Atree.Tables;
with Why.Conversions;    use Why.Conversions;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Gen.Expr;       use Why.Gen.Expr;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Progs;      use Why.Gen.Progs;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Gen.Records;    use Why.Gen.Records;
with Why.Inter;          use Why.Inter;

with Gnat2Why.Nodes;     use Gnat2Why.Nodes;
with Gnat2Why.Util;      use Gnat2Why.Util;
with Einfo; use Einfo;

package body Gnat2Why.Expr.Loops is

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Get_Loop_Invariant
     (Loop_Stmts      : Node_Lists.List;
      Initial_Stmts   : out Node_Lists.List;
      Loop_Invariants : out Node_Lists.List;
      Loop_Variants   : out Node_Lists.List;
      Final_Stmts     : out Node_Lists.List);
   --  Loop_Stmts is a flattened list of statements and declarations in a loop
   --  body. It includes the statements and declarations that appear directly
   --  in the main list inside the loop, and recursively all inner declarations
   --  and statements that appear in block statements.
   --
   --  Loop invariants (pragma Loop_Invariant) and loop variants (pragma
   --  Loop_Variant) may appear anywhere in this list.
   --
   --  Get_Loop_Invariant splits this list into four buckets:
   --   * Initial_Stmts is the list of initial statements and declarations
   --     before the first loop (in)variant, or the empty list if there are no
   --     loop (in)variant/variant in the loop.
   --   * Loop_Invariants is the list of loop invariants, if any, and the empty
   --     list otherwise. Note that Initial_Stmts and Final_Stmts do not
   --     contain any loop invariant.
   --   * Loop_Variants is the list of loop variants, if any, and the empty
   --     list otherwise. Note that Initial_Stmts and Final_Stmts do not
   --     contain any loop variant.
   --   * Final_Stmts is the list of final statements and declarations
   --     after the last select loop (in)variant, or all the statements of the
   --     loop if there is no loop (in)variant in the loop.

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id;
   --  Return the Defining_Identifier of the loop that belongs to an exit
   --  statement.

   procedure Transform_Loop_Variant
     (Stmt                  : Node_Id;
      Check_Prog            : out W_Prog_Id;
      Progress_Pred         : out W_Pred_Id;
      Same_Or_Progress_Pred : out W_Pred_Id;
      Tmp_Vars              : out Why_Node_Lists.List;
      Update_Prog           : out W_Prog_Id);
   --  Given a pragma Loop_Variant in Stmt, returns the Why node for checking
   --  that a loop variant does not raise run-time errors in Check_Prog;
   --  the Why node for the logic proposition that the variant increases
   --  or decreases as desired in Progress_Pred; the Why node for the logic
   --  proposition that the variant either progresses or stays the same in
   --  Same_Or_Progress_Pred. The last one is only used when the variant is
   --  not one of the "selected" ones. Update_Prog is a list of assignments of
   --  expression nodes in the loop variant to temporary names used to refer
   --  to their saved values, returned in Tmp_Vars.

   function Transform_Loop_Body_Statements
     (Stmts_And_Decls : Node_Lists.List) return W_Prog_Id;
   --  Returns Why nodes for the transformation of the list of statements and
   --  declaration Stmts_And_Decls from a loop body.

   function Wrap_Loop
     (Loop_Id            : Entity_Id;
      Loop_Start         : W_Prog_Id;
      Loop_End           : W_Prog_Id;
      Loop_Restart       : W_Prog_Id;
      Enter_Condition    : W_Prog_Id;
      Loop_Condition     : W_Prog_Id;
      Implicit_Invariant : W_Pred_Id;
      User_Invariant     : W_Pred_Id;
      Invariant_Check    : W_Prog_Id;
      Variant_Tmps       : Why_Node_Lists.List;
      Variant_Update     : W_Prog_Id;
      Variant_Check      : W_Prog_Id) return W_Prog_Id;
   --  Returns the loop expression in Why.
   --
   --  Loop_Start and Loop_End correspond to the statements and declarations
   --  respectively before and after the loop invariant pragma put by the
   --  user, if any. Otherwise, Loop_Start is the void expression, and
   --  Loop_End corresponds to all statements in the loop. Loop_Restart is the
   --  translation of Loop_Start adapted for being within the Why loop.
   --
   --  Enter_Condition and Loop_Condition are respectively the conditions
   --  for entering the loop the first time, and staying in the loop at
   --  each execution of the loop.
   --
   --  Implicit_Invariant is the condition that can be assumed to hold at the
   --  start of the Why loop. User_Invariant is the invariant to use for the
   --  Why loop. Invariant_Check is the Why program checking that the user
   --  invariant does not raise a run-time error.
   --
   --  Variant_Tmps is the list of temporary identifiers used to save the value
   --  of the loop variant expressions. Variant_Update assigns the current
   --  value of the loop variant expressions to these temporary variables.
   --  Variant_Check checks both the absence of run-time errors in the loop
   --  variant, and that the loop variant makes progress.
   --
   --  See comments in Wrap_Loop's body for the actual transformation.

   ------------------------
   -- Get_Loop_Invariant --
   ------------------------

   procedure Get_Loop_Invariant
     (Loop_Stmts      : Node_Lists.List;
      Initial_Stmts   : out Node_Lists.List;
      Loop_Invariants : out Node_Lists.List;
      Loop_Variants   : out Node_Lists.List;
      Final_Stmts     : out Node_Lists.List)
   is
      function Is_Last_Invariant_Or_Variant_In_Loop
        (N : Node_Id) return Boolean;
      --  Returns whether N is the last (in)variant in the loop

      ------------------------------------------
      -- Is_Last_Invariant_Or_Variant_In_Loop --
      ------------------------------------------

      function Is_Last_Invariant_Or_Variant_In_Loop
        (N : Node_Id) return Boolean
      is
         Cur : Node_Id := Next (N);
      begin
         while Present (Cur) loop
            if Is_Pragma_Check (Cur, Name_Loop_Invariant)
              or else Is_Pragma (Cur, Pragma_Loop_Variant)
            then
               return False;
            end if;

            Next (Cur);
         end loop;

         return True;
      end Is_Last_Invariant_Or_Variant_In_Loop;

      type State is
        (Before_Selected_Block, In_Selected_Block, Past_Selected_Block);

      Cur_State : State := Before_Selected_Block;
      N         : Node_Id;

      use Node_Lists;

   begin
      for Cur in Loop_Stmts.Iterate loop
         N := Element (Cur);

         case Cur_State is
            when Before_Selected_Block =>

               --  Add the first loop invariant to the selected ones, and
               --  update Cur_State.

               if Is_Pragma_Check (N, Name_Loop_Invariant) then
                  Loop_Invariants.Append (N);
                  Cur_State := In_Selected_Block;

               --  Add the first loop variant to the selected ones, and
               --  update Cur_State.

               elsif Is_Pragma (N, Pragma_Loop_Variant) then
                  Loop_Variants.Append (N);
                  Cur_State := In_Selected_Block;

               --  Add the statement or declaration to the initial ones

               else
                  Initial_Stmts.Append (N);
               end if;

            when In_Selected_Block =>

               --  Add any loop invariant to the selected ones

               if Is_Pragma_Check (N, Name_Loop_Invariant) then
                  Loop_Invariants.Append (N);

               --  Add any loop variant to the selected ones

               elsif Is_Pragma (N, Pragma_Loop_Variant) then
                  Loop_Variants.Append (N);

               --  Statements past the last (in)variant are included in the
               --  final list of statements, and Cur_State is updated.

               elsif Is_Last_Invariant_Or_Variant_In_Loop (N) then
                  Final_Stmts.Append (N);
                  Cur_State := Past_Selected_Block;

               --  Statements between (in)variants may have been introduced by
               --  the compiler for removing side-effects. Include these in the
               --  initial statements. Note that this may result in a failure
               --  to prove a run-time error in such statements while in fact
               --  this cannot happen at run time because a previous loop
               --  (in)variant would fail at run time, which is fine.

               else
                  pragma Assert (not Comes_From_Source (N));
                  Initial_Stmts.Append (N);
               end if;

            when Past_Selected_Block =>
               pragma Assert (not Is_Pragma_Check (N, Name_Loop_Invariant));
               pragma Assert (not Is_Pragma (N, Pragma_Loop_Variant));
               Final_Stmts.Append (N);
         end case;
      end loop;

      --  If no loop (in)variant was found, put all statements and declarations
      --  in the list Final_Stmts, leaving the list Initial_Stmts empty.

      if Cur_State = Before_Selected_Block then
         Final_Stmts.Move (Source => Initial_Stmts);
      end if;
   end Get_Loop_Invariant;

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
      Exc_Name    : constant W_Name_Id :=
        Loop_Exception_Name (Loop_Entity_Of_Exit_Statement (Stmt));
      Raise_Stmt  : constant W_Prog_Id :=
                      New_Raise
                        (Ada_Node => Stmt,
                         Name => Exc_Name);
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

   ------------------------------------
   -- Transform_Loop_Body_Statements --
   ------------------------------------

   function Transform_Loop_Body_Statements
     (Stmts_And_Decls : Node_Lists.List) return W_Prog_Id
   is
      Body_Prog : W_Prog_Id := New_Void;
   begin
      for Stmt_Or_Decl of Stmts_And_Decls loop

         --  Loop variants should not occur here anymore

         pragma Assert (not Is_Pragma (Stmt_Or_Decl, Pragma_Loop_Variant));

         Body_Prog := Transform_Statement_Or_Declaration_In_List
                        (Stmt_Or_Decl => Stmt_Or_Decl,
                         Prev_Prog    => Body_Prog);
      end loop;

      return Body_Prog;
   end Transform_Loop_Body_Statements;

   ------------------------------
   -- Transform_Loop_Statement --
   ------------------------------

   function Transform_Loop_Statement (Stmt : Node_Id) return W_Prog_Id is
      Loop_Body : constant List_Id   := Statements (Stmt);
      Scheme    : constant Node_Id   := Iteration_Scheme (Stmt);
      Loop_Id   : constant Entity_Id := Entity (Identifier (Stmt));

      Loop_Stmts      : Node_Lists.List;
      Initial_Stmts   : Node_Lists.List;
      Final_Stmts     : Node_Lists.List;
      Loop_Invariants : Node_Lists.List;
      Loop_Variants   : Node_Lists.List;

      Initial_Prog    : W_Prog_Id;
      Final_Prog      : W_Prog_Id;

      --  Variables for the selected loop invariants, default initialized to
      --  the proper values when the loop does not have an invariant.

      Inv_Check       : W_Prog_Id := New_Void;
      Invariant       : W_Pred_Id := True_Pred;

      --  Variable for the implicit invariant for dynamic properties of
      --  modified objects.

      Dyn_Types_Inv   : W_Pred_Id := True_Pred;

      --  Variables for the selected loop variants, default initialized to the
      --  proper values when the loop does not have a selected variant.

      Variant_Check   : W_Prog_Id := New_Void;
      Variant_Update  : W_Prog_Id := New_Void;
      Variant_Tmps    : Why_Node_Lists.List;

      Loop_Param_Ent  : Entity_Id := Empty;
      Loop_Index      : W_Identifier_Id;
      --  These two variables hold the loop parameter in Ada and Why, if any

   begin

      if Present (Scheme) and then
        not Present (Condition (Scheme)) and then
        Present (Loop_Parameter_Specification (Scheme))
      then
         Loop_Param_Ent :=
           Defining_Identifier (Loop_Parameter_Specification (Scheme));
         Loop_Index     :=
           To_Why_Id (E      => Loop_Param_Ent,
                      Domain => EW_Prog,
                      Typ    => EW_Int_Type);
         Ada_Ent_To_Why.Push_Scope (Symbol_Table);
         Insert_Entity (Loop_Param_Ent, Loop_Index, Mutable => True);
      end if;

      --  Retrieve the different parts of the loop

      Loop_Stmts := Get_Flat_Statement_And_Declaration_List (Loop_Body);
      Get_Loop_Invariant
        (Loop_Stmts      => Loop_Stmts,
         Initial_Stmts   => Initial_Stmts,
         Loop_Invariants => Loop_Invariants,
         Loop_Variants   => Loop_Variants,
         Final_Stmts     => Final_Stmts);

      --  Transform statements before and after the loop invariants

      Initial_Prog := Transform_Loop_Body_Statements (Initial_Stmts);
      Final_Prog   := Transform_Loop_Body_Statements (Final_Stmts);

      --  Generate the implicit invariant for the dynamic properties of objects
      --  modified in the loop.

      if Loop_Writes_Known (Loop_Id) then
         declare
            use Flow_Types;

            Modified : constant Flow_Id_Sets.Set :=
              To_Entire_Variables (Get_Loop_Writes (Loop_Id));
            N        : Node_Id;
            Dyn_Prop : W_Pred_Id;
            Expr     : W_Expr_Id;
            Binder   : Item_Type;
         begin
            for F of Modified loop
               if F.Kind = Direct_Mapping then
                  N := Get_Direct_Mapping_Id (F);
                  if Nkind (N) in N_Entity
                    and then Ekind (N) = E_Variable
                  then
                     Binder := Ada_Ent_To_Why.Element
                       (Symbol_Table, N);
                     Expr := (case Binder.Kind is
                                 when Regular =>
                                    New_Deref (Right => Binder.Main.B_Name,
                                               Typ   => Get_Type
                                                 (+Binder.Main.B_Name)),
                                 when UCArray =>
                                    New_Deref (Right => Binder.Content.B_Name,
                                               Typ   => Get_Type
                                                 (+Binder.Content.B_Name)),
                                 when DRecord =>
                                    Record_From_Split_Form (Binder, True),
                                 when Func    => raise Program_Error);
                     Dyn_Prop := Compute_Dynamic_Property
                       (Expr     => Expr,
                        Ty       => Etype (N),
                        Only_Var => True);

                     if Dyn_Prop /= True_Pred then
                        Dyn_Types_Inv :=
                          +New_And_Expr (Left   => +Dyn_Types_Inv,
                                         Right  => +Dyn_Prop,
                                         Domain => EW_Prog);
                     end if;
                  end if;
               end if;
            end loop;
         end;
      end if;

      --  Generate a VC for the loop invariants, located on the first one

      if not Loop_Invariants.Is_Empty then

         --  Generate the relevant bits for the various loop invariants

         for Loop_Invariant of Loop_Invariants loop
            declare
               One_Inv_Check : W_Prog_Id;
               One_Invariant : W_Pred_Id;
            begin
               Transform_Pragma_Check (Stmt    => Loop_Invariant,
                                       Runtime => One_Inv_Check,
                                       Pred    => One_Invariant);
               Inv_Check := Sequence (Inv_Check, One_Inv_Check);
               Invariant := +New_And_Expr (Left   => +Invariant,
                                           Right  => +One_Invariant,
                                           Domain => EW_Pred);
            end;
         end loop;

         Invariant := +New_VC_Expr (Ada_Node => Loop_Invariants.First_Element,
                                    Expr     => +Invariant,
                                    Reason   => VC_Loop_Invariant,
                                    Domain   => EW_Pred);
      end if;

      --  Generate the relevant bits for the loop variants, if any

      for Loop_Variant of Loop_Variants loop
         declare
            One_Variant_Prog   : W_Prog_Id;
            One_Variant_Pred   : W_Pred_Id;
            One_Variant_Update : W_Prog_Id;
            One_Variant_Tmps   : Why_Node_Lists.List;
            Unused_Pred        : W_Pred_Id;

         begin
            --  Generate the Why expressions for checking absence of run-time
            --  errors and variant progress.

            Transform_Loop_Variant
              (Stmt                  => Loop_Variant,
               Check_Prog            => One_Variant_Prog,
               Progress_Pred         => One_Variant_Pred,
               Same_Or_Progress_Pred => Unused_Pred,
               Tmp_Vars              => One_Variant_Tmps,
               Update_Prog           => One_Variant_Update);

            --  Add new temporaries to the common list for loop variants

            Append (To => Variant_Tmps, Elmts => One_Variant_Tmps);

            --  Create the program that updates the variables holding saved
            --  values of variant expressions.

            Variant_Update := Sequence (Variant_Update, One_Variant_Update);

            --  Combine the run-time check and the loop variant check in one
            --  program Variant_Check, for use in Loop_Wrap.

            Variant_Check :=
              Sequence
                ((1 => Variant_Check,
                  2 => New_Ignore (Prog => One_Variant_Prog),
                  3 => New_Located_Assert (Ada_Node => Loop_Variant,
                                           Pred     => One_Variant_Pred,
                                           Reason   => VC_Loop_Variant,
                                           Kind     => EW_Check)));
         end;
      end loop;

      --  Depending on the form of the loop, put together the generated Why
      --  nodes in a different way.

      --  Case of a simple loop

      if Nkind (Scheme) = N_Empty then
         return Wrap_Loop (Loop_Id            => Loop_Id,
                           Loop_Start         => Initial_Prog,
                           Loop_End           => Final_Prog,
                           Loop_Restart       => Initial_Prog,
                           Enter_Condition    => True_Prog,
                           Loop_Condition     => True_Prog,
                           Implicit_Invariant => Dyn_Types_Inv,
                           User_Invariant     => Invariant,
                           Invariant_Check    => Inv_Check,
                           Variant_Tmps       => Variant_Tmps,
                           Variant_Update     => Variant_Update,
                           Variant_Check      => Variant_Check);

      --  Case of a WHILE loop

      elsif Nkind (Iterator_Specification (Scheme)) = N_Empty
              and then
            Nkind (Loop_Parameter_Specification (Scheme)) = N_Empty
      then
         While_Loop : declare
            Cond_Prog : constant W_Prog_Id :=
              +Transform_Expr_With_Actions (Condition (Scheme),
                                            Condition_Actions (Scheme),
                                            EW_Bool_Type,
                                            EW_Prog,
                                            Params => Body_Params);
            Cond_Pred : constant W_Pred_Id :=
              +Transform_Expr_With_Actions (Condition (Scheme),
                                            Condition_Actions (Scheme),
                                            EW_Bool_Type,
                                            EW_Pred,
                                            Params => Body_Params);

            --  If the Loop_Assertion pragma comes first in the loop body
            --  (possibly inside nested block statements), then we can use the
            --  loop condition as an implicit invariant of the generated Why
            --  loop. In other cases, we cannot, as this would not be always
            --  correct.

            Impl_Pred : constant W_Pred_Id :=
              (if Get_Kind (+Initial_Prog) = W_Void then
                 Cond_Pred
               else
                  True_Pred);

            Impl_Inv  : constant W_Pred_Id :=
              +New_And_Expr (Left   => +Dyn_Types_Inv,
                             Right  => +Impl_Pred,
                             Domain => EW_Prog);
         begin
            return Wrap_Loop (Loop_Id            => Loop_Id,
                              Loop_Start         => Initial_Prog,
                              Loop_End           => Final_Prog,
                              Loop_Restart       => Initial_Prog,
                              Enter_Condition    => Cond_Prog,
                              Loop_Condition     => Cond_Prog,
                              Implicit_Invariant => Impl_Inv,
                              User_Invariant     => Invariant,
                              Invariant_Check    => Inv_Check,
                              Variant_Tmps       => Variant_Tmps,
                              Variant_Update     => Variant_Update,
                              Variant_Check      => Variant_Check);
         end While_Loop;

      --  Case of a FOR loop

      --  Here, we set the condition to express that the index is in the range
      --  of the loop. We need to evaluate the range expression once at the
      --  beginning of the loop, to get potential checks in that expression
      --  only once.

      elsif Nkind (Condition (Scheme)) = N_Empty then
         For_Loop : declare
            LParam_Spec  : constant Node_Id :=
                             Loop_Parameter_Specification (Scheme);
            Loop_Range   : constant Node_Id :=
              Discrete_Subtype_Definition (LParam_Spec);
            Is_Reverse   : constant Boolean := Reverse_Present (LParam_Spec);
            Index_Deref  : constant W_Prog_Id :=
                             New_Deref
                               (Ada_Node => Stmt,
                                Right    => +Loop_Index,
                                Typ      => EW_Int_Type);
            Update_Op    : constant EW_Binary_Op :=
                             (if Is_Reverse then EW_Substract
                              else EW_Add);
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

            Cond_Pred    : constant W_Pred_Id :=
              +Range_Expr (Loop_Range,
                           New_Deref (Right => Loop_Index, Typ => EW_Int_Type),
                           EW_Pred,
                           Params => Body_Params,
                           T_Type => EW_Int_Type);
            Actual_Range : constant Node_Id := Get_Range (Loop_Range);
            Low_Ident    : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => EW_Int_Type);
            High_Ident   : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => EW_Int_Type);
            Init_Index   : constant W_Identifier_Id :=
              (if Is_Reverse then High_Ident else Low_Ident);
            Exit_Index   : constant W_Identifier_Id :=
              (if Is_Reverse then Low_Ident else High_Ident);
            Exit_Cmp     : constant EW_Relation :=
              (if Is_Reverse then EW_Ge else EW_Le);
            Exit_Cond    : constant W_Expr_Id :=
              New_Relation (Domain  => EW_Prog,
                            Op_Type => EW_Int,
                            Op      => Exit_Cmp,
                            Left    => +Index_Deref,
                            Right   => +Exit_Index);
            Cond_Prog    : constant W_Prog_Id :=
              +New_Range_Expr (Domain    => EW_Prog,
                               Low       => +Low_Ident,
                               High      => +High_Ident,
                               Expr      => +Index_Deref);
            Impl_Inv  : constant W_Pred_Id :=
              +New_And_Expr (Left   => +Dyn_Types_Inv,
                             Right  => +Cond_Pred,
                             Domain => EW_Prog);
            Entire_Loop  : W_Prog_Id :=
              Wrap_Loop (Loop_Id            => Loop_Id,
                         Loop_Start         => Initial_Prog,
                         Loop_End           =>
                           Sequence (Final_Prog, Update_Stmt),
                         Loop_Restart       => Initial_Prog,
                         Enter_Condition    => Cond_Prog,
                         Loop_Condition     => +Exit_Cond,
                         Implicit_Invariant => Impl_Inv,
                         User_Invariant     => Invariant,
                         Invariant_Check    => Inv_Check,
                         Variant_Tmps       => Variant_Tmps,
                         Variant_Update     => Variant_Update,
                         Variant_Check      => Variant_Check);

         --  Start of For_Loop

         begin
            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
            Entire_Loop :=
              Sequence
                (New_Assignment
                     (Name => Loop_Index,
                      Value  => +Init_Index),
                 Entire_Loop);
            Entire_Loop :=
               +New_Typed_Binding
                 (Name    => High_Ident,
                  Domain  => EW_Prog,
                  Def     => +Transform_Expr (High_Bound (Actual_Range),
                                             EW_Int_Type,
                                             EW_Prog,
                                             Params => Body_Params),
                  Context => +Entire_Loop);
            Entire_Loop :=
              +New_Typed_Binding
                (Name    => Low_Ident,
                 Domain  => EW_Prog,
                 Def     =>
                   +Transform_Expr
                     (Low_Bound (Actual_Range),
                      EW_Int_Type,
                      EW_Prog,
                      Params => Body_Params),
                 Context => +Entire_Loop);

            --  For loop_parameter_specification whose
            --  discrete_subtype_definition is a subtype_indication,
            --  we generate a check that the range_constraint of the
            --  subtype_indication is compatible with the given subtype.

            if Nkind (Loop_Range) = N_Subtype_Indication then
               Entire_Loop :=
                 Sequence
                   (Assume_Of_Subtype_Indication
                      (Params   => Body_Params,
                       N        => Loop_Range,
                       Sub_Type => Etype (Defining_Identifier (LParam_Spec)),
                       Do_Check => True),
                    Entire_Loop);
            end if;

            return Entire_Loop;
         end For_Loop;

      else
         --  Some other kind of loop
         Ada.Text_IO.Put_Line ("[Transform_Loop_Statement] other loop");
         raise Not_Implemented;
      end if;
   end Transform_Loop_Statement;

   ----------------------------
   -- Transform_Loop_Variant --
   ----------------------------

   --  Given a pragma Loop_Variant of the form:

   --    pragma Loop_Variant (Dir1 => Expr1,
   --                         Dir2 => Expr2,
   --                             ...
   --                         Dirn => Exprn);

   --  Generates a Why program Check_Prog of the form:

   --    ignore (expr1);
   --    if expr1 = sav1 then
   --       (ignore (expr2);
   --        if expr2 = sav2 then
   --          ...
   --          ignore (exprn));

   --  where sav1, sav2 ... savn are the saved values of expr1, expr2 ... exprn
   --  at the start of each loop run, and at the point of occurrence of the
   --  loop variant. These names are returned in the list Tmp_Vars.

   --  and a Why proposition Progress_Pred of the form:

   --    expr1 op1 sav1 or (expr1 = sav1 and
   --                       expr2 op2 sav2 or (expr2 = sav2 and
   --                                          ...
   --                                          exprn opn savn))

   --  where op1, op2 ... opn is the operator < when the variant part is
   --  decreasing, and > when the variant part is increasing.

   --  and a Why proposition Same_Or_Progress_Pred of the form:

   --    expr1 op1 sav1 or (expr1 = sav1 and
   --                       expr2 op2 sav2 or (expr2 = sav2 and
   --                                          ...
   --                                          exprn opn savn or exprn = savn))

   --  where op1, op2 ... opn are like for Progress_Pred.

   --  Tmp_Assign is simply the list of assignments:

   --    sav1 := expr1;
   --    sav2 := expr2;
   --        ...
   --    savn := exprn

   procedure Transform_Loop_Variant
     (Stmt                  : Node_Id;
      Check_Prog            : out W_Prog_Id;
      Progress_Pred         : out W_Pred_Id;
      Same_Or_Progress_Pred : out W_Pred_Id;
      Tmp_Vars              : out Why_Node_Lists.List;
      Update_Prog           : out W_Prog_Id)
   is
      Variant : Node_Id;

      function Variant_Expr
        (Expr   : Node_Id;
         Domain : EW_Domain) return W_Expr_Id;
      --  Returns the value of the variant expression Expr as an int

      function Variant_Part_Does_Progress
        (Variant : Node_Id;
         Name    : W_Identifier_Id) return W_Pred_Id;
      --  Given a node Variant corresponding to a decreasing or increasing
      --  part in a loop variant, and a name Name to designate that expression,
      --  returns the Why term that corresponds to progress.

      function Variant_Part_Stays_Constant
        (Variant : Node_Id;
         Name    : W_Identifier_Id) return W_Pred_Id;
      --  Given a node Variant corresponding to a decreasing or increasing
      --  part in a loop variant, and a name Name to designate that expression,
      --  returns the Why term that expresses that it has not been modified.

      ------------------
      -- Variant_Expr --
      ------------------

      function Variant_Expr
        (Expr   : Node_Id;
         Domain : EW_Domain) return W_Expr_Id
      is
         Params : constant Transformation_Params :=
           (if Domain = EW_Prog then Body_Params else Assert_Params);
      begin
         return Transform_Expr (Expr          => Expr,
                                Expected_Type => EW_Int_Type,
                                Domain        => Domain,
                                Params        => Params);
      end Variant_Expr;

      --------------------------------
      -- Variant_Part_Does_Progress --
      --------------------------------

      function Variant_Part_Does_Progress
        (Variant : Node_Id;
         Name    : W_Identifier_Id) return W_Pred_Id
      is
         Expr : constant Node_Id := Expression (Variant);
         Cmp  : constant EW_Relation :=
           (if Chars (Variant) = Name_Decreases then EW_Lt else EW_Gt);
      begin
         return +New_Comparison (Cmp       => Cmp,
                                 Left      => Variant_Expr (Expr, EW_Term),
                                 Right     =>
                                   New_Deref (Right => +Name,
                                              Typ => EW_Int_Type),
                                 Domain    => EW_Pred);
      end Variant_Part_Does_Progress;

      ---------------------------------
      -- Variant_Part_Stays_Constant --
      ---------------------------------

      function Variant_Part_Stays_Constant
        (Variant : Node_Id;
         Name    : W_Identifier_Id) return W_Pred_Id
      is
         Expr : constant Node_Id := Expression (Variant);
      begin
         return +New_Comparison (Cmp       => EW_Eq,
                                 Left      => Variant_Expr (Expr, EW_Term),
                                 Right     =>
                                   New_Deref (Right => +Name,
                                              Typ => EW_Int_Type),
                                 Domain    => EW_Pred);
      end Variant_Part_Stays_Constant;

   --  Start of Transform_Loop_Variant

   begin
      --  Unused initialization to avoid compiler warning that variable may be
      --  used before being assigned to.

      Check_Prog := New_Void;
      Update_Prog := New_Void;
      Progress_Pred := True_Pred;
      Same_Or_Progress_Pred := True_Pred;

      --  Build incrementally Check_Prog and Logic_Part, assuming these
      --  variables already contain the Why nodes created for the variant
      --  cases that follow this one.

      --  Create a new name to designate the expression that is increasing or
      --  decreasing, and update Tmp_Vars and Update_Prog accordingly.

      Variant := Last (Pragma_Argument_Associations (Stmt));
      while Present (Variant) loop
         declare
            Name : constant W_Identifier_Id := New_Temp_Identifier;
            Expr : constant Node_Id := Expression (Variant);

            Pred_Progress : constant W_Pred_Id :=
              Variant_Part_Does_Progress (Variant, Name);
            Pred_Constant : constant W_Pred_Id :=
              Variant_Part_Stays_Constant (Variant, Name);
            Prog : constant W_Prog_Id :=
              New_Ignore (Prog => +Variant_Expr (Expr, EW_Prog));
            Assign : constant W_Assignment_Id :=
              New_Assignment (Name  => Name,
                              Value => +Variant_Expr (Expr, EW_Term));

         begin
            Tmp_Vars.Append (+Name);

            Update_Prog := Sequence (+Assign, Update_Prog);

            Check_Prog :=
              (if No (Next (Variant)) then
                 Prog
               else
                 Sequence (Prog,
                   +W_Expr_Id'(New_Conditional (Ada_Node    => Variant,
                                                Domain      => EW_Prog,
                                                Condition   => +Pred_Progress,
                                                Then_Part   => +Check_Prog))));

            Progress_Pred :=
              (if No (Next (Variant)) then
                 Pred_Progress
               else
                 +New_Or_Expr (Left   => +Pred_Progress,
                               Right  => New_And_Expr
                                           (Left   => +Pred_Constant,
                                            Right  => +Progress_Pred,
                                            Domain => EW_Pred),
                               Domain => EW_Pred));

            Same_Or_Progress_Pred :=
              (if No (Next (Variant)) then
                 +New_Or_Expr (Left   => +Pred_Progress,
                               Right  => +Pred_Constant,
                               Domain => EW_Pred)
               else
                 +New_Or_Expr (Left   => +Pred_Progress,
                               Right  => New_And_Expr
                                           (Left   => +Pred_Constant,
                                            Right  => +Progress_Pred,
                                            Domain => EW_Pred),
                               Domain => EW_Pred));
         end;

         Prev (Variant);
      end loop;
   end Transform_Loop_Variant;

   ---------------
   -- Wrap_Loop --
   ---------------

   --  Generate the following Why loop expression:
   --
   --  if enter_condition then
   --    try
   --      let loop_entry_tmps = saved_values in
   --      let variant_tmps = ref 0 in
   --        loop_start;
   --        loop invariant { user_invariant }
   --          assume { implicit_invariant };
   --          invariant_check;
   --          variant_update;
   --          loop_end;
   --          if loop_condition then
   --            loop_restart;
   --            variant_check
   --          else
   --            raise loop_name
   --        end loop
   --    with loop_name -> void
   --  end if
   --
   --  Note that the expression that checks that the user invariant does not
   --  raise a run-time error (invariant_check) is put inside the loop, in a
   --  context where the user invariant and the implicit invariant are known to
   --  hold. A naive translation would put it after the two copies of
   --  loop_start, but it is more efficient to put it in only one place. Both
   --  choices are logically equivalent, because the user invariant must be
   --  proved before it can be used in the loop.

   function Wrap_Loop
     (Loop_Id            : Entity_Id;
      Loop_Start         : W_Prog_Id;
      Loop_End           : W_Prog_Id;
      Loop_Restart       : W_Prog_Id;
      Enter_Condition    : W_Prog_Id;
      Loop_Condition     : W_Prog_Id;
      Implicit_Invariant : W_Pred_Id;
      User_Invariant     : W_Pred_Id;
      Invariant_Check    : W_Prog_Id;
      Variant_Tmps       : Why_Node_Lists.List;
      Variant_Update     : W_Prog_Id;
      Variant_Check      : W_Prog_Id) return W_Prog_Id
   is
      Loop_Ident : constant W_Name_Id := Loop_Exception_Name (Loop_Id);
      Loop_Inner : constant W_Prog_Id :=
        Sequence ((1 => Variant_Update,
                   2 => Loop_End,
                   3 => New_Conditional
                     (Condition => +Loop_Condition,
                      Then_Part => +Sequence (+Loop_Restart, +Variant_Check),
                      Else_Part => New_Raise (Name => Loop_Ident))));

      Loop_Body : constant W_Prog_Id :=
        Sequence ((1 => New_Assume_Statement
                          (Ada_Node => Empty, Post => Implicit_Invariant),
                   2 => Invariant_Check,
                   3 => Loop_Inner));

      Loop_Stmt : constant W_Prog_Id :=
        New_While_Loop
          (Condition    => True_Prog,
           Annotation   => New_Loop_Annot (Invariant => User_Invariant),
           Loop_Content => Loop_Body);

      Try_Body : constant W_Prog_Id :=
        Bind_From_Mapping_In_Expr
          (Params => Body_Params,
           Map    => Map_For_Loop_Entry (Loop_Id),
           Expr   => Create_Zero_Binding
                       (Vars => Variant_Tmps,
                        Prog => Sequence (Loop_Start, Loop_Stmt)));

      Loop_Try : constant W_Prog_Id :=
        New_Try_Block
          (Prog    => Try_Body,
           Handler => (1 => New_Handler (Name => Loop_Ident,
                                         Def  => New_Void)));
   begin
      return
        New_Conditional
          (Condition => +Enter_Condition,
           Then_Part => +Loop_Try);
   end Wrap_Loop;

end Gnat2Why.Expr.Loops;
