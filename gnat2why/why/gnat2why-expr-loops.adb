------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - E X P R - L O O P                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

with Debug;
with Gnat2Why_Args;
with Gnat2Why.Expr.Loops.Exits;
with Gnat2Why.Expr.Loops.Inv; use Gnat2Why.Expr.Loops.Inv;
with Gnat2Why.Util;           use Gnat2Why.Util;
with Namet;                   use Namet;
with Nlists;                  use Nlists;
with Opt;                     use type Opt.Warning_Mode_Type;
with Sinput;                  use Sinput;
with Snames;                  use Snames;
with SPARK_Util.Types;        use SPARK_Util.Types;
with Uintp;                   use Uintp;
with VC_Kinds;                use VC_Kinds;
with Why;                     use Why;
with Why.Atree.Builders;      use Why.Atree.Builders;
with Why.Atree.Modules;       use Why.Atree.Modules;
with Why.Atree.Tables;        use Why.Atree.Tables;
with Why.Conversions;         use Why.Conversions;
with Why.Gen.Expr;            use Why.Gen.Expr;
with Why.Gen.Names;           use Why.Gen.Names;
with Why.Gen.Preds;           use Why.Gen.Preds;
with Why.Gen.Progs;           use Why.Gen.Progs;
with Why.Inter;               use Why.Inter;

package body Gnat2Why.Expr.Loops is

   -----------------------
   -- Local Subprograms --
   -----------------------

   In_Loop_Initial_Statements : Boolean := False with Ghost;
   --  Ghost variable. True when analyzing the initial statements of a loop

   function Is_In_Loop_Initial_Statements return Boolean is
     (In_Loop_Initial_Statements);

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

   function Unroll_Loop
     (Loop_Id         : Entity_Id;
      Loop_Index      : W_Identifier_Id;
      Loop_Index_Type : W_Type_Id;
      Low_Val         : Uint;
      High_Val        : Uint;
      Reversed        : Boolean;
      Body_Prog       : W_Prog_Id)
      return W_Prog_Id;
   --  Returns the unrolled loop expression in Why3

   function Wrap_Loop
     (Loop_Id            : Entity_Id;
      Loop_Start         : W_Prog_Id;
      Loop_End           : W_Prog_Id;
      Loop_Restart       : W_Prog_Id;
      Enter_Condition    : W_Prog_Id;
      Exit_Condition     : W_Prog_Id;
      Implicit_Invariant : W_Pred_Id;
      User_Invariants    : W_Pred_Array;
      Invariant_Check    : W_Prog_Id;
      Variant_Tmps       : Why_Node_Lists.List;
      Variant_Update     : W_Prog_Id;
      Variant_Check      : W_Prog_Id;
      Update_Stmt        : W_Prog_Id := Why_Empty;
      Next_Stmt          : Node_Id := Empty)
      return W_Prog_Id;
   --  Returns the loop expression in Why
   --
   --  Loop_Start and Loop_End correspond to the statements and declarations
   --  respectively before and after the loop invariant pragma put by the
   --  user, if any. Otherwise, Loop_Start is the void expression, and
   --  Loop_End corresponds to all statements in the loop. Loop_Restart is the
   --  translation of Loop_Start adapted for being within the Why loop.
   --
   --  Enter_Condition and Exit_Condition are respectively the conditions for
   --  entering the loop the first time, and exiting the loop at each execution
   --  of the loop.
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
   --  See comments in Wrap_Loop's body for the actual transformation

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

      use Node_Lists;

   --  Start of processing for Get_Loop_Variant

   begin
      for N of Loop_Stmts loop
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

   function Get_Loop_Invariant (Loop_Stmt : Node_Id) return Node_Lists.List is
      Loop_Body       : constant List_Id := Statements (Loop_Stmt);
      Loop_Stmts      : Node_Lists.List;
      Initial_Stmts   : Node_Lists.List;
      Final_Stmts     : Node_Lists.List;
      Loop_Invariants : Node_Lists.List;
      Loop_Variants   : Node_Lists.List;
   begin
      Loop_Stmts := Get_Flat_Statement_And_Declaration_List (Loop_Body);
      Get_Loop_Invariant
        (Loop_Stmts      => Loop_Stmts,
         Initial_Stmts   => Initial_Stmts,
         Loop_Invariants => Loop_Invariants,
         Loop_Variants   => Loop_Variants,
         Final_Stmts     => Final_Stmts);
      return Loop_Invariants;
   end Get_Loop_Invariant;

   -----------------------------------
   -- Loop_Entity_Of_Exit_Statement --
   -----------------------------------

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id is
      function Is_Loop_Statement (N : Node_Id) return Boolean is
        (Nkind (N) = N_Loop_Statement);
      --  Returns True if N is a loop statement

      function Innermost_Loop_Stmt is new
        First_Parent_With_Property (Is_Loop_Statement);
   begin
      --  If the name is directly in the given node, return that name

      if Present (Name (N)) then
         return Entity (Name (N));

      --  Otherwise the exit statement belongs to the innermost loop, so
      --  simply go upwards (follow parent nodes) until we encounter the
      --  loop.

      else
         return Entity (Identifier (Innermost_Loop_Stmt (N)));
      end if;
   end Loop_Entity_Of_Exit_Statement;

   ------------------------------
   -- Transform_Exit_Statement --
   ------------------------------

   function Transform_Exit_Statement (Stmt : Node_Id) return W_Prog_Id
   is
      Exc_Name   : constant W_Name_Id :=
        Loop_Exception_Name (Loop_Entity_Of_Exit_Statement (Stmt));
      Raise_Stmt : constant W_Prog_Id :=
                     New_Raise
                       (Ada_Node => Stmt,
                        Name => Exc_Name);
   begin
      if No (Condition (Stmt)) then
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
      Body_Prog : W_Statement_Sequence_Id :=
        Void_Sequence;
   begin
      for Stmt_Or_Decl of Stmts_And_Decls loop

         --  Loop variants should not occur here anymore

         pragma Assert (not Is_Pragma (Stmt_Or_Decl, Pragma_Loop_Variant));

         Transform_Statement_Or_Declaration_In_List
           (Stmt_Or_Decl => Stmt_Or_Decl,
            Seq          => Body_Prog);
      end loop;

      return +Body_Prog;
   end Transform_Loop_Body_Statements;

   ------------------------------
   -- Transform_Loop_Statement --
   ------------------------------

   function Transform_Loop_Statement (Stmt : Node_Id) return W_Prog_Id is
      Loop_Body : constant List_Id   := Statements (Stmt);
      Scheme    : constant Node_Id   := Iteration_Scheme (Stmt);
      Loop_Id   : constant Entity_Id := Entity (Identifier (Stmt));
      Next_Stmt : constant Node_Id   := Next (Stmt);

      Loop_Stmts      : Node_Lists.List;
      Initial_Stmts   : Node_Lists.List;
      Final_Stmts     : Node_Lists.List;
      Loop_Invariants : Node_Lists.List;
      Loop_Variants   : Node_Lists.List;

      Initial_Prog    : W_Prog_Id;
      Final_Prog      : W_Prog_Id;

      --  Variables for the selected loop invariants, default initialized to
      --  the proper values when the loop does not have an invariant.

      Inv_Check       : W_Prog_Id := +Void;

      --  Variable for the implicit invariant for dynamic properties of
      --  modified objects.

      Dyn_Types_Inv   : W_Pred_Id := True_Pred;

      --  Variables for the selected loop variants, default initialized to the
      --  proper values when the loop does not have a selected variant.

      Variant_Check   : W_Prog_Id := +Void;
      Variant_Update  : W_Prog_Id := +Void;
      Variant_Tmps    : Why_Node_Lists.List;

      Loop_Param_Ent  : Entity_Id := Empty;
      Loop_Index      : W_Identifier_Id := Why_Empty;
      Loop_Index_Type : W_Type_Id := EW_Int_Type;
      --  These three variables hold the loop parameter in Ada and Why, if any

      --  Constants specific to range quantification

      Low_Id          : W_Identifier_Id := Why_Empty;
      High_Id         : W_Identifier_Id := Why_Empty;

   begin
      --  Push a scope for the exit statements of the loop. This
      --  scope is popped later by calling [Wrap_Loop] which calls
      --  [Exits.Wrap_Loop_Body].

      Exits.Before_Start_Of_Loop;

      --  Add the loop index to the entity table

      if Present (Scheme)
        and then No (Condition (Scheme))
      then
         if Present (Loop_Parameter_Specification (Scheme)) then
            Loop_Param_Ent  :=
              Defining_Identifier (Loop_Parameter_Specification (Scheme));
            Loop_Index_Type := Base_Why_Type_No_Bool (Loop_Param_Ent);
         else
            pragma Assert (Present (Iterator_Specification (Scheme)));
            Loop_Param_Ent :=
              Defining_Identifier (Iterator_Specification (Scheme));
            Loop_Index_Type := Type_Of_Node (Loop_Param_Ent);
         end if;

         Loop_Index := To_Why_Id (E      => Loop_Param_Ent,
                                  Domain => EW_Prog,
                                  Typ    => Loop_Index_Type);
         Ada_Ent_To_Why.Push_Scope (Symbol_Table);
         Insert_Entity (Loop_Param_Ent, Loop_Index, Mutable => True);

         Low_Id  := New_Temp_Identifier (Typ => Loop_Index_Type);
         High_Id := New_Temp_Identifier (Typ => Loop_Index_Type);
      end if;

      --  Retrieve the different parts of the loop

      Loop_Stmts := Get_Flat_Statement_And_Declaration_List (Loop_Body);
      Get_Loop_Invariant
        (Loop_Stmts      => Loop_Stmts,
         Initial_Stmts   => Initial_Stmts,
         Loop_Invariants => Loop_Invariants,
         Loop_Variants   => Loop_Variants,
         Final_Stmts     => Final_Stmts);

      declare
         Why_Invariants : W_Pred_Array (1 .. Integer (Loop_Invariants.Length));
         Save_Loop_Init : constant Boolean := In_Loop_Initial_Statements
           with Ghost;

      begin
         --  Transform statements before and after the loop invariants

         In_Loop_Initial_Statements := True;
         Initial_Prog := Transform_Loop_Body_Statements (Initial_Stmts);
         In_Loop_Initial_Statements := Save_Loop_Init;
         Final_Prog   := Transform_Loop_Body_Statements (Final_Stmts);

         --  Generate the implicit invariant for the dynamic properties of
         --  objects modified in the loop.

         Dyn_Types_Inv :=
           Generate_Frame_Condition
             (Stmt,
              Low_Id             => +Low_Id,
              High_Id            => +High_Id,
              Has_Loop_Invariant => not (Loop_Invariants.Is_Empty
                and then Loop_Variants.Is_Empty));

         --  Generate the loop invariants VCs

         if not Loop_Invariants.Is_Empty then
            declare
               Count : Natural := Natural (Loop_Invariants.Length);

            begin
               --  Generate the relevant bits for the various loop invariants.
               --  We consider loop invariants in reverse order, so that we can
               --  generate a cascade of conditionals to check RTE in a loop
               --  invariant only under the condition that previous loop
               --  invariants hold.

               for Loop_Invariant of reverse Loop_Invariants loop
                  declare
                     Expr          : Node_Id;
                     One_Inv_Check : W_Prog_Id;
                     One_Invariant : W_Pred_Id;
                     One_Inv_Var   : constant W_Identifier_Id :=
                       New_Temp_Identifier (Typ       => EW_Bool_Type,
                                            Base_Name => "inv");
                  begin
                     Transform_Pragma_Check (Stmt    => Loop_Invariant,
                                             Force   => False,
                                             Expr    => Expr,
                                             Runtime => One_Inv_Check,
                                             Pred    => One_Invariant);

                     --  Add checking of RTE in the Nth loop invariant, and use
                     --  it to guard the checking of RTE for (N+1)th and beyond
                     --  loop invariants.

                     Inv_Check :=
                       New_Binding (Name    => One_Inv_Var,
                                    Def     => +One_Inv_Check,
                                    Context =>
                                      +New_Ignore (Prog => Inv_Check));

                     --  Add the predicate for the Nth loop invariant

                     Why_Invariants (Count) :=
                       +New_VC_Expr (Ada_Node => Expr,
                                     Expr     => +One_Invariant,
                                     Reason   => VC_Loop_Invariant,
                                     Domain   => EW_Pred);
                     Count := Count - 1;
                  end;
               end loop;
            end;
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
               --  Generate the Why expressions for checking absence of
               --  run-time errors and variant progress.

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
         --  nodes in a different way. [Wrap_Loop] needs to be called on every
         --  path, as it takes care or popping the stack of exit paths by
         --  calling [Exits.Wrap_Loop_Body].

         --  Case of a simple loop

         if No (Scheme) then
            return Wrap_Loop (Loop_Id            => Loop_Id,
                              Loop_Start         => Initial_Prog,
                              Loop_End           => Final_Prog,
                              Loop_Restart       => Initial_Prog,
                              Enter_Condition    => True_Prog,
                              Exit_Condition     => False_Prog,
                              Implicit_Invariant => Dyn_Types_Inv,
                              User_Invariants    => Why_Invariants,
                              Invariant_Check    => Inv_Check,
                              Variant_Tmps       => Variant_Tmps,
                              Variant_Update     => Variant_Update,
                              Variant_Check      => Variant_Check,
                              Next_Stmt          => Next_Stmt);

         --  Case of a WHILE loop

         elsif Present (Condition (Scheme)) then
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
               --  (possibly inside nested block statements), then we can use
               --  the loop condition as an implicit invariant of the generated
               --  Why loop. In other cases, we cannot, as this would not be
               --  always correct.

               Impl_Pred : constant W_Pred_Id :=
                 (if Is_Essentially_Void (Initial_Prog)
                  then Cond_Pred
                  else True_Pred);

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
                                 Exit_Condition     => +W_Not_OId'(New_Not
                                   (Ada_Node => Condition (Scheme),
                                    Domain   => EW_Prog,
                                    Right    => +Cond_Prog)),
                                 Implicit_Invariant => Impl_Inv,
                                 User_Invariants    => Why_Invariants,
                                 Invariant_Check    => Inv_Check,
                                 Variant_Tmps       => Variant_Tmps,
                                 Variant_Update     => Variant_Update,
                                 Variant_Check      => Variant_Check,
                                 Next_Stmt          => Next_Stmt);
            end While_Loop;

         --  Case of a FOR loop

         --  Here, we set the condition to express that the index is in the
         --  range of the loop. We need to evaluate the range expression
         --  once at the beginning of the loop, to get potential checks
         --  in that expression only once.

         else
            pragma Assert (Present (Loop_Index));

            For_Loop : declare
               Over_Range   : constant Boolean :=
                 Present (Loop_Parameter_Specification (Scheme));
               --  For loops my iterate either on a range or on an iterator.

               LParam_Spec  : constant Node_Id :=
                 (if Over_Range then Loop_Parameter_Specification (Scheme)
                  else Iterator_Specification (Scheme));
               Over_Node    : constant Node_Id :=
                 (if Over_Range then Discrete_Subtype_Definition (LParam_Spec)
                  else Get_Container_In_Iterator_Specification (LParam_Spec));
               Index_Deref  : constant W_Prog_Id :=
                 New_Deref
                   (Ada_Node => Stmt,
                    Right    => +Loop_Index,
                    Typ      => Loop_Index_Type);

               --  Constants specific to iterator specification

               Typ_For_Cont : constant W_Type_Id :=
                 (if Over_Range then EW_Int_Type
                  else Type_Of_Node
                    (Etype (First_Formal
                     (Get_Iterable_Type_Primitive
                          (Etype (Over_Node), Name_First)))));
               W_Container  : constant W_Expr_Id :=
                 (if Over_Range then Why_Empty
                  else New_Temp_For_Expr
                    (Insert_Simple_Conversion
                         (Domain => EW_Prog,
                          Expr   => Transform_Expr
                            (Over_Node, EW_Prog, Body_Params),
                          To     => Typ_For_Cont),
                     Need_Temp =>
                        not SPARK_Atree.Is_Variable (Over_Node)));
               --  Introduce a temporary variable for the container expression
               --  except if it is a variable.
               W_Container_T : constant W_Expr_Id :=
                 (if Over_Range then Why_Empty
                  elsif SPARK_Atree.Is_Variable (Over_Node) then
                       Insert_Simple_Conversion
                         (Domain => EW_Term,
                          Expr   => Transform_Expr
                            (Over_Node, EW_Term, Body_Params),
                          To     => Typ_For_Cont)
                  else W_Container);
               --  Container expression in the term domain

               --  For for of loops, we need an identifier for the additional
               --  variable holding the iterator.

               Need_Iter    : constant Boolean :=
                 not Over_Range and then Of_Present (LParam_Spec);
               Typ_For_Iter : constant W_Type_Id :=
                 (if Need_Iter
                  then Type_Of_Node
                    (Get_Iterable_Type_Primitive
                         (Typ => Etype (Over_Node), Nam => Name_First))
                  else Loop_Index_Type);
               Nam_For_Iter : constant W_Identifier_Id :=
                 (if not Need_Iter then Loop_Index
                  else New_Temp_Identifier
                    (Ada_Node => Empty,
                     Typ      => Typ_For_Iter));
               Iter_Deref   : constant W_Prog_Id :=
                 New_Deref
                   (Ada_Node => Stmt,
                    Right    => +Nam_For_Iter,
                    Typ      => Typ_For_Iter);

               -------------------------------------
               -- Helper Subprograms for Iterable --
               -------------------------------------

               function Constraint_For_Iterable
                 (Domain : EW_Domain) return W_Expr_Id
               with
                 Pre => not Over_Range;
               --  @param Domain in which the constraint should be created
               --  @result Has_Element (W_Container, Iter_Deref)

               function Exit_Condition_For_Iterable return W_Expr_Id
               with
                 Pre => not Over_Range;
               --  @result not (Has_Element (W_Container, Next (Iter_Deref)))

               function Init_Iter return W_Prog_Id
               with
                 Pre => not Over_Range;
               --  @result First (W_Container)

               function Loop_Index_Value (Domain : EW_Domain) return W_Expr_Id
               with
                 Pre => not Over_Range and then Of_Present (LParam_Spec);
               --  @result Element (W_Container, Iter_Deref)

               function Update_Index return W_Prog_Id
               with
                 Pre => not Over_Range and then Of_Present (LParam_Spec);
               --  @result if Has_Element (W_Container, Iter_Deref)
               --       then Loop_Index := Element (W_Container, Iter_Deref)

               -----------------------------
               -- Constraint_For_Iterable --
               -----------------------------

               function Constraint_For_Iterable
                 (Domain : EW_Domain) return W_Expr_Id is
                  H_Elmt   : constant Entity_Id :=
                    Get_Iterable_Type_Primitive
                      (Etype (Over_Node), Name_Has_Element);
                  W_H_Elmt : constant W_Identifier_Id :=
                    +Transform_Identifier
                              (Params => Body_Params,
                               Expr   => H_Elmt,
                               Ent    => H_Elmt,
                               Domain => Domain);
                  Cur_Expr  : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain         => EW_Term,
                       Expr           => +Iter_Deref,
                       To             => Typ_For_Iter,
                       Force_No_Slide => True);
               begin
                  if Domain in EW_Prog | EW_Pterm then
                     pragma Assert (W_Container /= Why_Empty);
                     return +New_VC_Call
                       (Ada_Node => LParam_Spec,
                        Name     => W_H_Elmt,
                        Progs    => (1 => W_Container,
                                     2 => Cur_Expr),
                        Reason   => VC_Precondition,
                        Domain   => Domain,
                        Typ      => EW_Bool_Type);
                  else
                     pragma Assert (W_Container_T /= Why_Empty);
                     return New_Function_Call
                       (Ada_Node => LParam_Spec,
                        Domain   => Domain,
                        Subp     => H_Elmt,
                        Name     => W_H_Elmt,
                        Args     => (1 => W_Container_T,
                                     2 => Cur_Expr),
                        Typ      => EW_Bool_Type);
                  end if;
               end Constraint_For_Iterable;

               ---------------------------------
               -- Exit_Condition_For_Iterable --
               ---------------------------------

               function Exit_Condition_For_Iterable return W_Expr_Id is
                  H_Elmt   : constant Entity_Id :=
                    Get_Iterable_Type_Primitive
                      (Etype (Over_Node), Name_Has_Element);
                  W_H_Elmt : constant W_Identifier_Id :=
                    +Transform_Identifier
                    (Params => Body_Params,
                     Expr   => H_Elmt,
                     Ent    => H_Elmt,
                     Domain => EW_Prog);
                  N_Elmt   : constant Entity_Id :=
                    Get_Iterable_Type_Primitive
                      (Etype (Over_Node), Name_Next);
                  W_N_Elmt : constant W_Identifier_Id :=
                    +Transform_Identifier
                    (Params => Body_Params,
                     Expr   => N_Elmt,
                     Ent    => N_Elmt,
                     Domain => EW_Prog);
                  Cur_Expr  : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain         => EW_Term,
                       Expr           => +Iter_Deref,
                       To             => Typ_For_Iter,
                       Force_No_Slide => True);
               begin
                  pragma Assert (W_Container /= Why_Empty);
                  return
                    +W_Not_Id'(New_Not
                               (Ada_Node => LParam_Spec,
                                Domain   => EW_Prog,
                                Right    =>
                                  +New_VC_Call
                                  (Ada_Node => LParam_Spec,
                                   Name     => W_H_Elmt,
                                   Progs    =>
                                     (1 => W_Container,
                                      2 => +New_VC_Call
                                        (Ada_Node => LParam_Spec,
                                         Name     => W_N_Elmt,
                                         Progs    => (1 => W_Container,
                                                      2 => Cur_Expr),
                                         Reason   => VC_Precondition,
                                         Domain   => EW_Prog,
                                         Typ      => EW_Bool_Type)),
                                   Reason   => VC_Precondition,
                                   Domain   => EW_Prog,
                                   Typ      => EW_Bool_Type)));
               end Exit_Condition_For_Iterable;

               ---------------
               -- Init_Iter --
               ---------------

               function Init_Iter return W_Prog_Id is
                  First      : constant Entity_Id :=
                    Get_Iterable_Type_Primitive
                      (Etype (Over_Node), Name_First);

                  pragma Assert (W_Container /= Why_Empty);

                  Call_First : constant W_Expr_Id := +New_VC_Call
                    (Ada_Node => LParam_Spec,
                     Name     =>
                       W_Identifier_Id
                         (Transform_Identifier
                              (Params => Body_Params,
                               Expr   => First,
                               Ent    => First,
                               Domain => EW_Prog)),
                     Progs    => (1 => W_Container),
                     Reason   => VC_Precondition,
                     Domain   => EW_Prog,
                     Typ      => Typ_For_Iter);
               begin
                  return +Call_First;
               end Init_Iter;

               ----------------------
               -- Loop_Index_Value --
               ----------------------

               function Loop_Index_Value (Domain : EW_Domain) return W_Expr_Id
               is
                  Elmt     : constant Entity_Id :=
                    Get_Iterable_Type_Primitive
                      (Etype (Over_Node), Name_Element);
                  Cur_Expr : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain         => EW_Term,
                       Expr           => +Iter_Deref,
                       To             => Typ_For_Iter,
                       Force_No_Slide => True);
                  W_Elmt   : constant W_Identifier_Id :=
                    +Transform_Identifier
                      (Params => Body_Params,
                       Expr   => Elmt,
                       Ent    => Elmt,
                       Domain => Domain);
               begin
                  if Domain in EW_Prog | EW_Pterm then
                     pragma Assert (W_Container /= Why_Empty);
                     return New_VC_Call
                       (Ada_Node => LParam_Spec,
                        Name     => W_Elmt,
                        Progs    =>
                          (1 => W_Container,
                           2 => Cur_Expr),
                        Reason   => VC_Precondition,
                        Domain   => EW_Prog,
                        Typ      => Type_Of_Node (Etype (Elmt)));
                  else
                     pragma Assert (W_Container_T /= Why_Empty);
                     return New_Function_Call
                       (Ada_Node => LParam_Spec,
                        Domain   => Domain,
                        Subp     => Elmt,
                        Name     => W_Elmt,
                        Args     =>
                          (1 => W_Container_T,
                           2 => Cur_Expr),
                        Typ      => Type_Of_Node (Etype (Elmt)));
                  end if;
               end Loop_Index_Value;

               ------------------
               -- Update_Index --
               ------------------

               function Update_Index return W_Prog_Id is
                  Call_Elmt : constant W_Prog_Id :=
                    +Loop_Index_Value (EW_Prog);
                  Upd_Elmt  : constant W_Expr_Id :=
                    New_Conditional
                      (Domain    => EW_Prog,
                       Condition =>
                         Constraint_For_Iterable (EW_Prog),
                       Then_Part =>
                         New_Assignment
                           (Ada_Node => Stmt,
                            Name     => Loop_Index,
                            Labels   => Name_Id_Sets.Empty_Set,
                            Value    => +Insert_Simple_Conversion
                              (Domain         => EW_Term,
                               Expr           => +Call_Elmt,
                               To             => Loop_Index_Type,
                               Force_No_Slide => True),
                            Typ      => Loop_Index_Type));
               begin
                  return +Upd_Elmt;
               end Update_Index;

               -----------------------
               -- Local Subprograms --
               -----------------------

               function Construct_Cond return W_Prog_Id;
               --  @return Condition to enter the loop

               function Construct_Exit_Cond return W_Prog_Id;
               --  @return Condition to exit the loop

               function Construct_Init_Prog return W_Prog_Id;
               --  @return Initialization of Loop_Index

               function Construct_Inv_For_Index return W_Pred_Id;
               --  @return Implicit loop invariant about Loop_Index and
               --  Nam_For_Iter

               function Construct_Update_Stmt return W_Prog_Id;
               --  @return Update of Loop_Index and Nam_For_Iter when necessary

               --------------------
               -- Construct_Cond --
               --------------------

               function Construct_Cond return W_Prog_Id is
               begin
                  if Over_Range then

                     --  Low_Id <= Index_Deref <= High_Id

                     return +New_Range_Expr (Domain => EW_Prog,
                                             Low    => +Low_Id,
                                             High   => +High_Id,
                                             Expr   => +Index_Deref);
                  else

                     --  Has_Element (W_Container, Iter_Deref)

                     return +Constraint_For_Iterable (EW_Prog);
                  end if;
               end Construct_Cond;

               -------------------------
               -- Construct_Exit_Cond --
               -------------------------

               function Construct_Exit_Cond return W_Prog_Id is
               begin
                  if Over_Range then

                     --  Index_Deref = Low_Id if Is_Reverse
                     --  Index_Deref = High_Id otherwise

                     declare
                        Is_Reverse : constant Boolean :=
                          Reverse_Present (LParam_Spec);
                        Exit_Index : constant W_Expr_Id :=
                          (if Is_Reverse then +Low_Id else +High_Id);
                        Eq_Symb    : constant W_Identifier_Id :=
                          (if Why_Type_Is_BitVector (Loop_Index_Type) then
                                MF_BVs (Loop_Index_Type).Prog_Eq
                           else Why_Eq);
                        Exit_Cond  : constant W_Expr_Id :=
                          New_Call (Domain => EW_Prog,
                                    Name   => Eq_Symb,
                                    Typ    => EW_Bool_Type,
                                    Args   => (+Index_Deref, +Exit_Index));
                     begin
                        return +Exit_Cond;
                     end;
                  else

                     --  not (Has_Element (W_Container, Next (Iter_Deref)));

                     return +Exit_Condition_For_Iterable;
                  end if;
               end Construct_Exit_Cond;

               -------------------------
               -- Construct_Init_Prog --
               -------------------------

               function Construct_Init_Prog return W_Prog_Id is
               begin
                  if Over_Range then

                     --  Loop_Index := High_Id if Is_Reverse
                     --  Loop_Index := Low_Id otherwise

                     declare
                        Is_Reverse : constant Boolean :=
                          Reverse_Present (LParam_Spec);
                        Init_Index : constant W_Expr_Id :=
                          (if Is_Reverse then +High_Id else +Low_Id);
                     begin
                        return New_Assignment
                          (Name   => Loop_Index,
                           Value  => +Init_Index,
                           Labels => Name_Id_Sets.Empty_Set,
                           Typ    => Loop_Index_Type);
                     end;
                  else
                     if Need_Iter then

                        --  if Has_Element (W_Container, Iter_Deref) then
                        --    Loop_Index := Element (W_Container, Iter_Deref)

                        return Update_Index;
                     else

                        --  Loop_Index := First (W_Container)

                        return New_Assignment
                          (Name   => Nam_For_Iter,
                           Value  => Init_Iter,
                           Labels => Name_Id_Sets.Empty_Set,
                           Typ    => Typ_For_Iter);
                     end if;
                  end if;
               end Construct_Init_Prog;

               -----------------------------
               -- Construct_Inv_For_Index --
               -----------------------------

               function Construct_Inv_For_Index return W_Pred_Id is
               begin
                  if Over_Range then

                     --  In the range expression of the invariant, explicitly
                     --  set T_Type to handle the special case of
                     --  Standard.Boolean, where bounds and index are of
                     --  different base types (bool for bounds, int for index).

                     return
                       +Range_Expr (Over_Node,
                                    New_Deref (Right => Loop_Index,
                                               Typ   => Loop_Index_Type),
                                    EW_Pred,
                                    Params => Body_Params,
                                    T_Type => Loop_Index_Type);

                  elsif Need_Iter then

                     --  Has_Element (W_Container, Iter_Deref) and then
                     --    Index_Deref = Element (W_Container, Iter_Deref)

                     declare
                        H_Elmt    : constant W_Expr_Id :=
                          Constraint_For_Iterable (EW_Pred);
                        Elmt_Iter : constant W_Expr_Id :=
                          New_Comparison
                            (Why_Eq,
                             +Index_Deref,
                             Loop_Index_Value (EW_Term),
                             EW_Pred);
                     begin
                        return W_Pred_Id (New_And_Then_Expr
                                          (H_Elmt, Elmt_Iter, EW_Pred));
                     end;
                  else

                     --  Has_Element (W_Container, Iter_Deref)

                     return +Constraint_For_Iterable (EW_Pred);
                  end if;
               end Construct_Inv_For_Index;

               ---------------------------
               -- Construct_Update_Stmt --
               ---------------------------

               function Construct_Update_Stmt return W_Prog_Id is
               begin
                  if Over_Range then

                     --  Loop_Index := Index_Deref - 1 if Is_Reverse
                     --  Loop_Index := Index_Deref + 1 otherwise

                     declare
                        Is_Reverse  : constant Boolean :=
                          Reverse_Present (LParam_Spec);
                        Update_Op   : constant W_Identifier_Id :=
                          (if Why_Type_Is_BitVector (Loop_Index_Type) then
                               (if Is_Reverse then
                                   MF_BVs (Loop_Index_Type).Sub
                                else
                                   MF_BVs (Loop_Index_Type).Add)
                           else
                             (if Is_Reverse then Int_Infix_Subtr
                              else Int_Infix_Add));
                        One_Expr    : constant W_Expr_Id :=
                          (if Why_Type_Is_BitVector (Loop_Index_Type) then
                                New_Modular_Constant
                             (Ada_Node => Stmt,
                              Value    => Uint_1,
                              Typ      => Loop_Index_Type)
                           else
                              New_Integer_Constant
                             (Ada_Node => Stmt,
                              Value    => Uint_1));
                        Update_Expr : constant W_Prog_Id :=
                          New_Call
                            (Ada_Node => Stmt,
                             Name     => Update_Op,
                             Args     =>
                               (1 => +Index_Deref,
                                2 => One_Expr),
                             Typ      => Loop_Index_Type);
                     begin
                        return New_Assignment
                          (Ada_Node => Stmt,
                           Name     => Loop_Index,
                           Labels   => Name_Id_Sets.Empty_Set,
                           Value    => +Update_Expr,
                           Typ      => Loop_Index_Type);
                     end;
                  else
                     declare
                        Next      : constant Entity_Id :=
                          Get_Iterable_Type_Primitive
                            (Etype (Over_Node), Name_Next);
                        Cur_Expr  : constant W_Expr_Id :=
                          Insert_Simple_Conversion
                            (Domain         => EW_Term,
                             Expr           => +Iter_Deref,
                             To             => Typ_For_Iter,
                             Force_No_Slide => True);
                        Call_Next : constant W_Expr_Id := +New_VC_Call
                          (Ada_Node => LParam_Spec,
                           Name     =>
                             W_Identifier_Id
                               (Transform_Identifier
                                    (Params => Body_Params,
                                     Expr   => Next,
                                     Ent    => Next,
                                     Domain => EW_Prog)),
                           Progs    => (1 => W_Container,
                                        2 => Cur_Expr),
                           Reason   => VC_Precondition,
                           Domain   => EW_Prog,
                           Typ      => Typ_For_Iter);
                        Upd_Next  : constant W_Prog_Id :=
                          New_Assignment
                            (Ada_Node => Stmt,
                             Name     => Nam_For_Iter,
                             Labels   => Name_Id_Sets.Empty_Set,
                             Value    => +Insert_Simple_Conversion
                               (Domain         => EW_Term,
                                Expr           => +Call_Next,
                                To             => Get_Type (+Iter_Deref),
                                Force_No_Slide => True),
                             Typ      => Typ_For_Iter);
                     begin
                        if Need_Iter then

                           --  Nam_For_Iter := Next (W_Container, Iter_Deref)
                           --  Loop_Index := Element (W_Container, Iter_Deref)

                           return Sequence (Upd_Next, Update_Index);
                        else

                           --  Nam_For_Iter := Next (W_Container, Iter_Deref)

                           return Upd_Next;
                        end if;
                     end;
                  end if;
               end Construct_Update_Stmt;

               ---------------------
               -- Local Variables --
               ---------------------

               Index_Inv   : constant W_Pred_Id := Construct_Inv_For_Index;
               Cond_Prog   : constant W_Prog_Id := Construct_Cond;
               Update_Stmt : constant W_Prog_Id :=
                 +Insert_Cnt_Loc_Label (Stmt, +Construct_Update_Stmt);
               Exit_Cond   : constant W_Prog_Id := Construct_Exit_Cond;
               Impl_Inv    : constant W_Pred_Id :=
                 +New_And_Expr (Left   => +Dyn_Types_Inv,
                                Right  => +Index_Inv,
                                Domain => EW_Prog);

               Entire_Loop : W_Prog_Id;

               --  Variables used in loop unrolling
               Low_Val  : Uint;
               High_Val : Uint;
               Unroll   : Unrolling_Type;

            --  Start of processing for For_Loop

            begin
               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

               --  Special case of a FOR loop without loop (in)variant on a
               --  static range, which can be unrolled for every value of the
               --  loop index.

               Candidate_For_Loop_Unrolling
                 (Loop_Stmt   => Stmt,
                  Output_Info =>
                    Debug.Debug_Flag_Underscore_F
                      and not Gnat2Why_Args.No_Loop_Unrolling,
                  Result      => Unroll,
                  Low_Val     => Low_Val,
                  High_Val    => High_Val);

               if not Gnat2Why_Args.No_Loop_Unrolling
                 and then Unroll /= No_Unrolling
               then
                  declare
                     Inlined_Body : constant W_Prog_Id :=
                       (if Unroll = Unrolling_With_Condition then
                           New_Conditional (Condition => +Cond_Prog,
                                            Then_Part => +Final_Prog)
                        else Final_Prog);
                  begin
                     Entire_Loop :=
                       Unroll_Loop (Loop_Id         => Loop_Id,
                                    Loop_Index      => Loop_Index,
                                    Loop_Index_Type => Loop_Index_Type,
                                    Low_Val         => Low_Val,
                                    High_Val        => High_Val,
                                    Reversed        =>
                                      Reverse_Present (LParam_Spec),
                                    Body_Prog       => Inlined_Body);
                  end;

               --  Regular case of a FOR loop with a loop (in)variant, or no
               --  static bounds, requiring a proof by induction.

               else
                  Entire_Loop :=
                    Wrap_Loop (Loop_Id            => Loop_Id,
                               Loop_Start         => Initial_Prog,
                               Loop_End           => Final_Prog,
                               Loop_Restart       => Initial_Prog,
                               Enter_Condition    => Cond_Prog,
                               Exit_Condition     => Exit_Cond,
                               Implicit_Invariant => Impl_Inv,
                               User_Invariants    => Why_Invariants,
                               Invariant_Check    => Inv_Check,
                               Variant_Tmps       => Variant_Tmps,
                               Variant_Update     => Variant_Update,
                               Variant_Check      => Variant_Check,
                               Update_Stmt        => Update_Stmt,
                               Next_Stmt          => Next_Stmt);

                  Entire_Loop :=
                    Sequence
                      (Construct_Init_Prog,
                       Entire_Loop);
               end if;

               --  Create new variable for iterator if needed

               if Need_Iter then
                  Entire_Loop :=
                    New_Binding_Ref
                      (Name    => Nam_For_Iter,
                       Def     => Init_Iter,
                       Context => Entire_Loop,
                       Typ     => Typ_For_Iter);
               end if;

               --  Bind the temporary variable used for the container
               --  expression if any.

               if W_Container /= Why_Empty then
                  Entire_Loop :=
                    +Binding_For_Temp (Ada_Node => Loop_Id,
                                       Domain   => EW_Prog,
                                       Tmp      => W_Container,
                                       Context  => +Entire_Loop);
               end if;

               --  Add let bindings for bounds

               if Over_Range then
                  declare
                     Actual_Range : constant Node_Id :=
                       Get_Range (Over_Node);
                     High_Expr    : constant W_Expr_Id :=
                       Transform_Expr (High_Bound (Actual_Range),
                                       Loop_Index_Type,
                                       EW_Prog,
                                       Params => Body_Params);
                     Low_Expr     : constant W_Expr_Id :=
                       Transform_Expr (Low_Bound (Actual_Range),
                                       Loop_Index_Type,
                                       EW_Prog,
                                       Params => Body_Params);
                  begin
                     --  Insert assignment to high bound first, so that
                     --  assignment to low bound is done prior to assignment to
                     --  high bound in generated Why3 code. This ensures that a
                     --  common error is detected on low bound rather than high
                     --  bound, which is more intuitive.

                     Entire_Loop := +New_Typed_Binding
                       (Stmt, EW_Prog, High_Id, High_Expr, +Entire_Loop);
                     Entire_Loop := +New_Typed_Binding
                       (Stmt, EW_Prog, Low_Id, Low_Expr, +Entire_Loop);
                  end;
               end if;

               --  For loop_parameter_specification whose
               --  discrete_subtype_definition is a subtype_indication,
               --  we generate a check that the range_constraint of the
               --  subtype_indication is compatible with the given subtype.

               if Nkind (Over_Node) = N_Subtype_Indication then
                  Entire_Loop :=
                    Sequence
                      (Check_Subtype_Indication
                         (Params   => Body_Params,
                          N        => Over_Node,
                          Sub_Type =>
                            Etype (Defining_Identifier (LParam_Spec))),
                       Entire_Loop);
               end if;

               return Entire_Loop;
            end For_Loop;
         end if;
      end;
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
         Name    : W_Identifier_Id;
         Domain  : EW_Domain) return W_Expr_Id;
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
                                Expected_Type =>
                                  Base_Why_Type_No_Bool (Expr),
                                Domain        => Domain,
                                Params        => Params);
      end Variant_Expr;

      --------------------------------
      -- Variant_Part_Does_Progress --
      --------------------------------

      function Variant_Part_Does_Progress
        (Variant : Node_Id;
         Name    : W_Identifier_Id;
         Domain  : EW_Domain) return W_Expr_Id
      is
         Expr : constant Node_Id := Expression (Variant);
         WTyp : constant W_Type_Id := Base_Why_Type_No_Bool (Expr);
         Cmp  : constant W_Identifier_Id :=
           (if Chars (Variant) = Name_Decreases
            then (if Why_Type_Is_BitVector (WTyp)
              then MF_BVs (WTyp).Ult
              else Int_Infix_Lt)
            else (if Why_Type_Is_BitVector (WTyp)
              then MF_BVs (WTyp).Ugt
              else Int_Infix_Gt));
         Sub_Domain : constant EW_Domain :=
           (if Domain = EW_Pred then EW_Term else Domain);
      begin
         return
           New_Comparison
           (Symbol => Cmp,
            Left   => Variant_Expr (Expr, Sub_Domain),
            Right  => New_Deref (Right => +Name,
                                 Typ   => WTyp),
            Domain => Domain);
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
         return
           +New_Comparison
           (Symbol => Why_Eq,
            Left   => Variant_Expr (Expr, EW_Term),
            Right  =>
              New_Deref (Right => +Name,
                         Typ   => Base_Why_Type_No_Bool (Expr)),
            Domain => EW_Pred);
      end Variant_Part_Stays_Constant;

   --  Start of processing for Transform_Loop_Variant

   begin
      --  Unused initialization to avoid compiler warning that variable may be
      --  used before being assigned to.

      Check_Prog := +Void;
      Update_Prog := +Void;
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
            Expr : constant Node_Id := Expression (Variant);
            Name : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => Base_Why_Type_No_Bool (Expr));

            Pred_Progress : constant W_Pred_Id :=
              +Variant_Part_Does_Progress (Variant, Name, EW_Pred);
            Prog_Progress : constant W_Prog_Id :=
              +Variant_Part_Does_Progress (Variant, Name, EW_Pterm);
            Pred_Constant : constant W_Pred_Id :=
              Variant_Part_Stays_Constant (Variant, Name);
            Prog : constant W_Prog_Id :=
              New_Ignore (Prog => +Variant_Expr (Expr, EW_Prog));
            Assign : constant W_Assignment_Id :=
              New_Assignment (Name   => Name,
                              Value  => +Variant_Expr (Expr, EW_Pterm),
                              Labels => Name_Id_Sets.Empty_Set,
                              Typ    => Base_Why_Type_No_Bool (Expr));

         begin
            Tmp_Vars.Append (+Name);

            Update_Prog := Sequence (+Assign, Update_Prog);

            Check_Prog :=
              (if No (Next (Variant)) then
                 Prog
               else
                 Sequence (Prog,
                   +W_Expr_Id'(New_Conditional (Ada_Node  => Variant,
                                                Domain    => EW_Prog,
                                                Condition => +Prog_Progress,
                                                Then_Part => +Check_Prog))));

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

   -----------------
   -- Unroll_Loop --
   -----------------

   function Unroll_Loop
     (Loop_Id         : Entity_Id;
      Loop_Index      : W_Identifier_Id;
      Loop_Index_Type : W_Type_Id;
      Low_Val         : Uint;
      High_Val        : Uint;
      Reversed        : Boolean;
      Body_Prog       : W_Prog_Id)
      return W_Prog_Id
   is
      function Repeat_Loop return W_Prog_Id;
      --  Repeat the loop body for each value of the index

      -----------------
      -- Repeat_Loop --
      -----------------

      function Repeat_Loop return W_Prog_Id is
         First_Val : constant Uint := (if Reversed then High_Val else Low_Val);
         Last_Val  : constant Uint := (if Reversed then Low_Val else High_Val);
         Cur_Val   : Uint;
         Cur_Cst   : W_Prog_Id;

         Stmt_List : W_Prog_Array
           (1 .. 2 * (Integer (UI_To_Int (High_Val) -
                               UI_To_Int (Low_Val) + 1)));
         Cur_Idx   : Positive;

      begin
         Cur_Val := First_Val;
         Cur_Idx := 1;
         loop
            Cur_Cst :=
              (if Why_Type_Is_BitVector (Loop_Index_Type) then
                 New_Modular_Constant
                   (Value => Cur_Val,
                    Typ   => Loop_Index_Type)
               else
                 New_Integer_Constant (Value => Cur_Val));
            Stmt_List (Cur_Idx) :=
              New_Assignment
                (Name   => Loop_Index,
                 Value  => Cur_Cst,
                 Labels => Name_Id_Sets.Empty_Set,
                 Typ    => Loop_Index_Type);
            Cur_Idx := Cur_Idx + 1;
            Stmt_List (Cur_Idx) := Body_Prog;
            Cur_Idx := Cur_Idx + 1;

            exit when Cur_Val = Last_Val;

            if Reversed then
               Cur_Val := Cur_Val - 1;
            else
               Cur_Val := Cur_Val + 1;
            end if;
         end loop;

         return Sequence (Stmt_List);
      end Repeat_Loop;

      ---------------------
      -- Local Variables --
      ---------------------

      Loop_Ident : constant W_Name_Id := Loop_Exception_Name (Loop_Id);

      Try_Body : constant W_Prog_Id :=
        Bind_From_Mapping_In_Expr
          (Params => Body_Params,
           Map    => Map_For_Loop_Entry (Loop_Id),
           Expr   => Sequence
             (New_Comment
               (Comment =>
                  NID ("Unrolling of the loop statements"
                    & (if Sloc (Loop_Id) > 0 then
                         " of loop " & Build_Location_String
                        (Sloc (Loop_Id))
                      else ""))),
               Repeat_Loop));

      Loop_Try : constant W_Prog_Id :=
        New_Try_Block
          (Prog    => Try_Body,
           Handler => (1 => New_Handler (Name => Loop_Ident,
                                         Def  => +Void)));
   begin
      return Sequence
        (New_Comment
           (Comment => NID ("Translation of an Ada loop"
            & (if Sloc (Loop_Id) > 0 then
                 " from " & Build_Location_String (Sloc (Loop_Id))
              else ""))),
         Loop_Try);
   end Unroll_Loop;

   ---------------
   -- Wrap_Loop --
   ---------------

   --  Generate the following Why loop expression:
   --
   --  if enter_condition then
   --    try
   --      [try]
   --        let loop_entry_tmps = saved_values in
   --        let variant_tmps = ref 0 in
   --          loop_start;
   --          invariant_check;
   --          loop invariant { user_invariant }
   --            assume { implicit_invariant };
   --            variant_update;
   --            loop_end;
   --            if exit_condition then
   --              raise loop_name;
   --            [Update_Stmt;]
   --            loop_restart;
   --            variant_check;
   --            invariant_check;
   --          end loop
   --      [with exit_path_1 -> path_1
   --         | ...
   --         | exit_path_n -> path_n]
   --    with loop_name -> void
   --  end if
   --
   --  Note that the expression that checks that the user invariant does
   --  not raise a run-time error is duplicated after [loop_start] and
   --  [loop_restart]. An earlier design inserted it only once at the beginning
   --  of the loop, but it led to unprovable runtime checks in some loop
   --  invariants, because it did not benefit from the knowledge of the loop
   --  invariant (including the implicit part) modified by the body of the
   --  loop.
   --
   --  The inner try-catch block is only generated if needed for handling exit
   --  paths. In that case, the exit path inside the loop has been replaced
   --  by raising the corresponding exception. The declaration for these
   --  exceptions is done at subprogram level.

   function Wrap_Loop
     (Loop_Id            : Entity_Id;
      Loop_Start         : W_Prog_Id;
      Loop_End           : W_Prog_Id;
      Loop_Restart       : W_Prog_Id;
      Enter_Condition    : W_Prog_Id;
      Exit_Condition     : W_Prog_Id;
      Implicit_Invariant : W_Pred_Id;
      User_Invariants    : W_Pred_Array;
      Invariant_Check    : W_Prog_Id;
      Variant_Tmps       : Why_Node_Lists.List;
      Variant_Update     : W_Prog_Id;
      Variant_Check      : W_Prog_Id;
      Update_Stmt        : W_Prog_Id := Why_Empty;
      Next_Stmt          : Node_Id := Empty)
      return W_Prog_Id
   is
      Loop_Ident : constant W_Name_Id := Loop_Exception_Name (Loop_Id);
      Loop_Inner : constant W_Prog_Id :=
        Sequence ((1 => Variant_Update,
                   2 => New_Comment
                     (Comment => NID ("Loop statements appearing after the"
                      & " loop invariant"
                      & (if Sloc (Loop_Id) > 0 then
                           " of loop " & Build_Location_String (Sloc (Loop_Id))
                         else ""))),
                   3 => Loop_End,
                   4 => New_Comment
                     (Comment => NID ("Check for the exit condition and loop"
                      & " statements appearing before the loop invariant"
                      & (if Sloc (Loop_Id) > 0 then
                           " of loop " & Build_Location_String (Sloc (Loop_Id))
                         else ""))),
                   5 => New_Conditional
                          (Condition => +Exit_Condition,
                           Then_Part => New_Raise (Name => Loop_Ident)),
                   6 => (if Update_Stmt = Why_Empty then
                           +Void
                         else
                           Update_Stmt),
                   7 => Loop_Restart,
                   8 => Variant_Check,
                   9 => Invariant_Check));

      Loop_Body : constant W_Prog_Id :=
        Sequence ((1 => New_Comment
                   (Comment => NID ("Assume implicit invariants from the loop"
                    & (if Sloc (Loop_Id) > 0 then
                         " " & Build_Location_String (Sloc (Loop_Id))
                      else ""))),
                   2 => New_Assume_Statement (Pred => Implicit_Invariant),
                   3 => New_Comment
                     (Comment =>
                          NID ("Check for absence of RTE in the invariant"
                        & (if Sloc (Loop_Id) > 0 then
                             " of loop " & Build_Location_String
                            (Sloc (Loop_Id))
                          else ""))),
                   4 => Loop_Inner));

      Loop_Stmt : constant W_Prog_Id :=
        New_While_Loop
          (Ada_Node     => Loop_Id,
           Condition    => True_Prog,
           Invariants   => User_Invariants,
           Loop_Content => Loop_Body);

      Try_Body : W_Prog_Id :=
        Bind_From_Mapping_In_Expr
          (Params => Body_Params,
           Map    => Map_For_Loop_Entry (Loop_Id),
           Expr   => Create_Zero_Binding
                       (Vars => Variant_Tmps,
                        Prog => Sequence
                          ((1 => New_Comment
                            (Comment =>
                                 NID ("First unroling of the loop statements"
                               & " appearing before the loop invariant"
                               & (if Sloc (Loop_Id) > 0 then
                                    " of loop " & Build_Location_String
                                   (Sloc (Loop_Id))
                                  else ""))),
                            2 => Loop_Start,
                            3 => New_Comment
                              (Comment =>
                                   NID ("While loop translating the Ada loop"
                                 & (if Sloc (Loop_Id) > 0 then
                                      " from " & Build_Location_String
                                     (Sloc (Loop_Id))
                                    else ""))),
                            4 => Invariant_Check,
                            5 => Loop_Stmt))));

      Loop_Try : W_Prog_Id;
      Warn_Dead_Code : W_Prog_Id := +Void;

   begin
      --  Possibly wrap the loop body in a first try-catch block to handle exit
      --  paths from the loop.

      Exits.Wrap_Loop_Body (Try_Body);

      --  Now wrap the resulting program in the main try-catch block for the
      --  loop, catching the exception corresponding to exiting the loop.

      Loop_Try := New_Try_Block
        (Prog    => Try_Body,
         Handler => (1 => New_Handler (Name => Loop_Ident,
                                       Def  => +Void)));

      if Present (Next_Stmt)
        --  Do not issue a check for dead code if switch --proof-warnings is
        --  not set
        and then Gnat2Why_Args.Proof_Warnings
        --  or if warnings are suppressed
        and then Opt.Warning_Mode /= Opt.Suppress
        --  or when the next statement if an inconditional error, signaled as
        --  either a raise statement or a pragma Assert (False).
        and then not Is_Error_Signaling_Statement (Next_Stmt)
      then
         Warn_Dead_Code :=
           +New_VC_Expr
             (Ada_Node => Next_Stmt,
              Expr     => +New_Identifier (Name => "absurd"),
              Reason   => VC_Dead_Code,
              Domain   => EW_Prog);

         Warn_Dead_Code :=
           Sequence
             (New_Comment
                (Comment => NID ("Check dead code after loop"
                 & (if Sloc (Next_Stmt) > 0 then
                      " at " & Build_Location_String (Sloc (Next_Stmt))
                   else ""))),
              New_Ignore (Prog => Warn_Dead_Code));
      end if;

      return
        Sequence
          ((1 => New_Comment
                  (Comment =>
                     NID ("Translation of an Ada loop"
                          & (if Sloc (Loop_Id) > 0 then
                              " from " & Build_Location_String (Sloc (Loop_Id))
                             else ""))),
            2 => New_Conditional (Condition => +Enter_Condition,
                                  Then_Part => +Loop_Try),
            3 => Warn_Dead_Code));
   end Wrap_Loop;

end Gnat2Why.Expr.Loops;
