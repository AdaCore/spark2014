------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - E X P R - L O O P                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
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

with Ada.Strings.Unbounded;   use Ada.Strings.Unbounded;
with Gnat2Why_Args;
with Gnat2Why.Error_Messages; use Gnat2Why.Error_Messages;
with Gnat2Why.Expr.Loops.Inv; use Gnat2Why.Expr.Loops.Inv;
with Gnat2Why.Subprograms;    use Gnat2Why.Subprograms;
with Gnat2Why.Util;           use Gnat2Why.Util;
with Namet;                   use Namet;
with Nlists;                  use Nlists;
with Opt;
use type Opt.Warning_Mode_Type;
with Sinput;                  use Sinput;
with Snames;                  use Snames;
with SPARK_Util.Hardcoded;    use SPARK_Util.Hardcoded;
with Uintp;                   use Uintp;
with VC_Kinds;                use VC_Kinds;
with Why;                     use Why;
with Why.Atree.Accessors;     use Why.Atree.Accessors;
with Why.Atree.Builders;      use Why.Atree.Builders;
with Why.Atree.Modules;       use Why.Atree.Modules;
with Why.Conversions;         use Why.Conversions;
with Why.Gen.Binders;         use Why.Gen.Binders;
with Why.Gen.Expr;            use Why.Gen.Expr;
with Why.Gen.Names;           use Why.Gen.Names;
with Why.Gen.Progs;           use Why.Gen.Progs;
with Why.Inter;               use Why.Inter;

package body Gnat2Why.Expr.Loops is

   -----------------------
   -- Local Subprograms --
   -----------------------

   In_Loop_Initial_Statements : Boolean := False
   with Ghost;
   --  Ghost variable. True when analyzing the initial statements of a loop

   Imprecise_Constants : Entity_Sets.Set;
   --  Scalar constants occurring before loop invariants in enclosing loops
   --  whose value is not precisely known after the invariant. This set is
   --  maintained by Transform_Loop_Statement so it always contains constants
   --  whose value is not precisely known at the analyzed program point.

   function Is_In_Loop_Initial_Statements return Boolean
   is (In_Loop_Initial_Statements);

   procedure Get_Loop_Invariant
     (Loop_Stmts          : Node_Lists.List;
      Initial_Stmts       : out Node_Lists.List;
      Loop_Invariants     : out Node_Lists.List;
      Loop_Variants       : out Node_Lists.List;
      Final_Stmts         : out Node_Lists.List;
      Frame_Constants     : out Entity_Sets.Set;
      Imprecise_Constants : out Entity_Sets.Set);
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
   --   * Frame_Constants is the set of all (scalar) constants declared just
   --     before the invariant. Their values are assumed in the invariant.
   --   * Imprecise_Constants is the set of other (scalar) constants declared
   --     before the invariant. Their values might not be known after the
   --     invariant.

   function Transform_Loop_Variant
     (Stmt : N_Pragma_Id; Params : Transformation_Params) return W_Variants_Id;
   --  Given a pragma Loop_Variant in Stmt, returns the Variants Why3 node that
   --  contains the same information in Why3 syntax (the variant expression as
   --  a term).

   function Check_Loop_Variant
     (Stmt : N_Pragma_Id; Params : Transformation_Params) return W_Prog_Id;
   --  Given a pragma Loop_Variant in Stmt, returns the Why node for checking
   --  that a loop variant does not raise run-time errors.

   function Transform_Loop_Body_Statements
     (Instrs : Node_Lists.List; Params : Transformation_Params)
      return W_Prog_Id;
   --  Returns Why nodes for the transformation of the list of statements and
   --  declaration Instrs from a loop body.

   function Unroll_Loop
     (Loop_Id         : E_Loop_Id;
      Loop_Index      : W_Identifier_Id;
      Loop_Index_Type : W_Type_Id;
      Low_Val         : Uint;
      High_Val        : Uint;
      Reversed        : Boolean;
      Body_Prog       : W_Prog_Id;
      Params          : Transformation_Params) return W_Prog_Id;
   --  Returns the unrolled loop expression in Why3

   function Wrap_Loop
     (Loop_Id            : E_Loop_Id;
      Loop_Start         : W_Prog_Id;
      Loop_End           : W_Prog_Id;
      Enter_Condition    : W_Prog_Id;
      Exit_Condition     : W_Prog_Id;
      Implicit_Invariant : W_Pred_Id;
      User_Invariants    : W_Pred_Array;
      Invariant_Check    : W_Prog_Id;
      Variants           : W_Variants_Array;
      Variant_Check      : W_Prog_Id;
      Update_Stmt        : W_Prog_Id := Why_Empty;
      First_Stmt         : Node_Id;
      Next_Stmt          : Node_Id := Empty;
      Last_Inv           : Opt_N_Pragma_Id := Empty;
      Params             : Transformation_Params) return W_Prog_Id;
   --  Returns the loop expression in Why
   --
   --  Loop_Start and Loop_End correspond to the statements and declarations
   --  respectively before and after the loop invariant pragma put by the
   --  user, if any. Otherwise, Loop_Start is the void expression, and
   --  Loop_End corresponds to all statements in the loop.
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
   --  Variants is the list of Variants nodes (which themselves are lists of
   --  Increases/Decreases items). Variant_Check checks the absence of run-time
   --  errors in the loop variant.
   --
   --  First_Stmt is the first statement in the loop body, to help decide
   --  whether to issue a dead code warning. Similarly, Next_Stmt is the first
   --  statement after the loop, to help decide whether to issue a dead code
   --  warning if control cannot reach that point.
   --
   --  See comments in Wrap_Loop's body for the actual transformation

   ------------------------
   -- Check_Loop_Variant --
   ------------------------

   function Check_Loop_Variant
     (Stmt : N_Pragma_Id; Params : Transformation_Params) return W_Prog_Id
   is
      Prog          : W_Prog_Id := +Void;
      Variant       : Opt_N_Pragma_Argument_Association_Id;
      Assert_Params : constant Transformation_Params :=
        (Params with delta Phase => Generate_VCs_For_Assert);
   begin
      Variant := First (Pragma_Argument_Associations (Stmt));

      while Present (Variant) loop
         declare
            Expr   : constant N_Subexpr_Id := Expression (Variant);
            W_Expr : W_Prog_Id :=
              Transform_Prog
                (Expr          => Expr,
                 Expected_Type => Base_Why_Type_No_Bool (Expr),
                 Params        => Assert_Params);

         begin
            --  If Expr is a big integer, insert a check to make sure that the
            --  value stays non-negative.

            if Chars (Variant) /= Name_Structural
              and then not Has_Discrete_Type (Etype (Expr))
            then
               pragma
                 Assert
                   (Is_From_Hardcoded_Unit
                      (Base_Type (Etype (Expr)), Big_Integers));

               declare
                  Tmp : constant W_Expr_Id := New_Temp_For_Expr (+W_Expr);
               begin
                  W_Expr :=
                    Sequence
                      (New_Located_Assert
                         (Ada_Node => Expr,
                          Pred     =>
                            New_Comparison
                              (Symbol => Int_Infix_Ge,
                               Left   => +Tmp,
                               Right  =>
                                 New_Integer_Constant (Value => Uint_0)),
                          Reason   => VC_Range_Check,
                          Kind     => EW_Assert),
                       +Tmp);

                  W_Expr :=
                    +Binding_For_Temp
                       (Ada_Node => Expr,
                        Domain   => EW_Prog,
                        Tmp      => Tmp,
                        Context  => +W_Expr);
               end;
            end if;

            Append (Prog, New_Ignore (Prog => W_Expr));
            Next (Variant);
         end;
      end loop;
      return Prog;
   end Check_Loop_Variant;

   ---------------------------------------------
   -- Get_Flat_Statement_And_Declaration_List --
   ---------------------------------------------

   function Get_Flat_Statement_And_Declaration_List
     (Stmts : List_Id) return Node_Lists.List
   is

      function Contains_Loop_Invariant (Block_Stmt : Node_Id) return Boolean;
      --  Return True if Block_Stmt contains loop invariants or variants,
      --  either directly or in a nested block statement.

      ------------------------------
      --  Contains_Loop_Invariant --
      ------------------------------

      Blocks : Node_To_Bool_Maps.Map;
      --  Map to memoize the results on nested blocks so that the code is
      --  traversed at most twice in Get_Flat_Statement_And_Declaration_List.

      function Contains_Loop_Invariant (Block_Stmt : Node_Id) return Boolean is
         Position     : constant Node_To_Bool_Maps.Cursor :=
           Blocks.Find (Block_Stmt);
         Cur_Stmt     : Node_Id := First (Declarations (Block_Stmt));
         Decl_Scanned : Boolean := False;
         --  Track progress to go over main loop twice,
         --  once for declaration, once for statements.
         --  Loop invariants are allowed in both (SRM 5.5.{5,6}).

      begin
         --  If Block_Stmt as already been traversed, return immediately

         if Node_To_Bool_Maps.Has_Element (Position) then
            return Node_To_Bool_Maps.Element (Position);
         end if;

         return Found : Boolean := False do
            Main :
            loop
               while No (Cur_Stmt) loop
                  --  Loop to handle potential case of neither declarations
                  --  nor statements.

                  exit Main when Decl_Scanned;
                  Decl_Scanned := True;
                  Cur_Stmt :=
                    First
                      (Statements (Handled_Statement_Sequence (Block_Stmt)));
               end loop;

               case Nkind (Cur_Stmt) is
                  when N_Block_Statement =>
                     if Contains_Loop_Invariant (Cur_Stmt) then
                        Found := True;
                        exit Main;
                     end if;

                  when N_Pragma =>
                     if Is_Pragma_Check (Cur_Stmt, Name_Loop_Invariant)
                       or else Is_Pragma (Cur_Stmt, Pragma_Loop_Variant)
                     then
                        Found := True;
                        exit Main;
                     end if;

                  when others =>
                     null;
               end case;

               Nlists.Next (Cur_Stmt);
            end loop Main;

            Blocks.Insert (Block_Stmt, Found);
         end return;
      end Contains_Loop_Invariant;

      Cur_Stmt   : Node_Id := Nlists.First (Stmts);
      Flat_Stmts : Node_Lists.List;

      --  Start of processing for Get_Flat_Statement_And_Declaration_List

   begin
      while Present (Cur_Stmt) loop
         case Nkind (Cur_Stmt) is
            when N_Block_Statement =>
               if Contains_Loop_Invariant (Cur_Stmt) then
                  if Present (Declarations (Cur_Stmt)) then
                     Append
                       (Flat_Stmts,
                        Get_Flat_Statement_And_Declaration_List
                          (Declarations (Cur_Stmt)));
                  end if;

                  Append
                    (Flat_Stmts,
                     Get_Flat_Statement_And_Declaration_List
                       (Statements (Handled_Statement_Sequence (Cur_Stmt))));

                  --  We should never expand blocks which have exception
                  --  handlers.

                  pragma
                    Assert
                      (No
                         (Exception_Handlers
                            (Handled_Statement_Sequence (Cur_Stmt))));
               else
                  Flat_Stmts.Append (Cur_Stmt);
               end if;

            --  We should never expand blocks which contain declarations
            --  requiring a special handling at the end of the enclosing
            --  scope (ie local borrowers and objects which need reclamation).

            when N_Object_Declaration =>
               pragma
                 Assert
                   (not Is_Local_Borrower (Defining_Identifier (Cur_Stmt))
                      and then not Contains_Allocated_Parts
                                     (Etype (Defining_Identifier (Cur_Stmt))));
               Flat_Stmts.Append (Cur_Stmt);

            when others =>
               Flat_Stmts.Append (Cur_Stmt);
         end case;

         Nlists.Next (Cur_Stmt);
      end loop;

      return Flat_Stmts;
   end Get_Flat_Statement_And_Declaration_List;

   ------------------------
   -- Get_Loop_Invariant --
   ------------------------

   procedure Get_Loop_Invariant
     (Loop_Stmts          : Node_Lists.List;
      Initial_Stmts       : out Node_Lists.List;
      Loop_Invariants     : out Node_Lists.List;
      Loop_Variants       : out Node_Lists.List;
      Final_Stmts         : out Node_Lists.List;
      Frame_Constants     : out Entity_Sets.Set;
      Imprecise_Constants : out Entity_Sets.Set)
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

                  --  Store all constant encountered before the invariant in
                  --  Frame_Constants. When a statement is encountered, move
                  --  constants from Frame_Constants to Imprecise_Constants.

                  if Nkind (N) = N_Object_Declaration
                    and then Ekind (Defining_Identifier (N)) = E_Constant
                  then
                     Frame_Constants.Insert (Defining_Identifier (N));

                  elsif Nkind (N) not in N_Declaration | N_Ignored_In_SPARK
                    and then not Frame_Constants.Is_Empty
                  then
                     Imprecise_Constants.Union (Frame_Constants);
                     Frame_Constants.Clear;
                  end if;
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

               --  Ignore pragmas Annotate in the list of loop pragmas,
               --  typically used to justify unproved loop pragmas.

               elsif Is_Pragma (N, Pragma_Annotate) then
                  null;

               --  Statements between (in)variants may have been introduced by
               --  the compiler for removing side effects. Include these in the
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
      --  in the list Final_Stmts, leaving the list Initial_Stmts empty. Also
      --  clear the Frame_Constants and Imprecise_Constants sets.

      if Cur_State = Before_Selected_Block then
         Final_Stmts.Move (Source => Initial_Stmts);
         Frame_Constants.Clear;
         Imprecise_Constants.Clear;
      end if;
   end Get_Loop_Invariant;

   function Get_Loop_Invariant
     (Loop_Stmt : N_Loop_Statement_Id) return Node_Lists.List
   is
      Loop_Body           : constant List_Id := Statements (Loop_Stmt);
      Loop_Stmts          : Node_Lists.List;
      Initial_Stmts       : Node_Lists.List;
      Final_Stmts         : Node_Lists.List;
      Loop_Invariants     : Node_Lists.List;
      Loop_Variants       : Node_Lists.List;
      Frame_Constants     : Entity_Sets.Set;
      Imprecise_Constants : Entity_Sets.Set;
   begin
      Loop_Stmts := Get_Flat_Statement_And_Declaration_List (Loop_Body);
      Get_Loop_Invariant
        (Loop_Stmts          => Loop_Stmts,
         Initial_Stmts       => Initial_Stmts,
         Loop_Invariants     => Loop_Invariants,
         Loop_Variants       => Loop_Variants,
         Final_Stmts         => Final_Stmts,
         Frame_Constants     => Frame_Constants,
         Imprecise_Constants => Imprecise_Constants);
      return Loop_Invariants;
   end Get_Loop_Invariant;

   --------------------------------------
   -- Imprecise_Constant_Value_In_Loop --
   --------------------------------------

   function Imprecise_Constant_Value_In_Loop (E : Entity_Id) return Boolean
   is (Imprecise_Constants.Contains (E));

   ------------------------------------
   -- Transform_Loop_Body_Statements --
   ------------------------------------

   function Transform_Loop_Body_Statements
     (Instrs : Node_Lists.List; Params : Transformation_Params)
      return W_Prog_Id
   is
      Body_Prog : W_Statement_Sequence_Id := Void_Sequence;
   begin
      for Instr of Instrs loop

         --  Loop variants should not occur here anymore

         pragma Assert (not Is_Pragma (Instr, Pragma_Loop_Variant));

         Transform_Statement_Or_Declaration_In_List
           (Stmt_Or_Decl => Instr, Params => Params, Seq => Body_Prog);
      end loop;

      return +Body_Prog;
   end Transform_Loop_Body_Statements;

   -----------------------------------
   -- Transform_Loop_Jump_Statement --
   -----------------------------------

   function Transform_Loop_Jump_Statement
     (Stmt : Node_Id; Params : Transformation_Params) return W_Prog_Id
   is
      Exc_Name   : constant W_Name_Id :=
        Loop_Exception_Name
          (Loop_Entity_Of_Loop_Jump_Statement (Stmt),
           Is_Continue => Stmt in N_Continue_Statement_Id);
      Raise_Stmt : W_Prog_Id := New_Raise (Ada_Node => Stmt, Name => Exc_Name);
   begin
      Prepend (Finalization_Actions_On_Jump (Stmt, Params), Raise_Stmt);

      if No (Condition (Stmt)) then
         return Raise_Stmt;
      else
         return
           New_Conditional
             (Ada_Node  => Stmt,
              Condition =>
                Transform_Prog (Condition (Stmt), EW_Bool_Type, Params),
              Then_Part => +Raise_Stmt);
      end if;
   end Transform_Loop_Jump_Statement;

   ------------------------------
   -- Transform_Loop_Statement --
   ------------------------------

   function Transform_Loop_Statement
     (Stmt : N_Loop_Statement_Id; Params : Transformation_Params)
      return W_Prog_Id
   is
      function Transform_Loop_Variants
        (List : Node_Lists.List) return W_Variants_Array;

      function Check_Loop_Variants (List : Node_Lists.List) return W_Prog_Id;

      -------------------------
      -- Check_Loop_Variants --
      -------------------------

      function Check_Loop_Variants (List : Node_Lists.List) return W_Prog_Id is
         Stmts   : W_Prog_Array (1 .. Natural (List.Length));
         Counter : Positive := 1;
      begin
         if List.Is_Empty then
            return +Void;
         end if;

         for Variant of List loop
            Stmts (Counter) := Check_Loop_Variant (Variant, Params);
            Counter := Counter + 1;
         end loop;

         return Sequence (Stmts);
      end Check_Loop_Variants;

      -----------------------------
      -- Transform_Loop_Variants --
      -----------------------------

      function Transform_Loop_Variants
        (List : Node_Lists.List) return W_Variants_Array
      is
         Variants_Ar : W_Variants_Array (1 .. Natural (List.Length));
         Count       : Natural := 0;
      begin
         for Loop_Variant of List loop

            --  Structural variants are checked statically

            if Chars (First (Pragma_Argument_Associations (Loop_Variant)))
              = Name_Structural
            then
               declare
                  Variant : constant Node_Id :=
                    First (Pragma_Argument_Associations (Loop_Variant));

               begin
                  pragma Assert (No (Next (Variant)));
                  pragma
                    Assert
                      (Nkind (Expression (Variant))
                       in N_Identifier | N_Expanded_Name);

                  declare
                     Result      : Boolean;
                     Explanation : Unbounded_String;
                  begin
                     Structurally_Decreases_In_Loop
                       (Brower      => Entity (Expression (Variant)),
                        Loop_Stmt   => Stmt,
                        Result      => Result,
                        Explanation => Explanation);
                     Emit_Static_Proof_Result
                       (Node        => Loop_Variant,
                        Kind        => VC_Loop_Variant,
                        Proved      => Result,
                        E           => Current_Subp,
                        Explanation => To_String (Explanation));
                  end;
               end;
            else
               Count := Count + 1;
               Variants_Ar (Count) :=
                 Transform_Loop_Variant (Loop_Variant, Params);
            end if;
         end loop;
         return Variants_Ar (1 .. Count);
      end Transform_Loop_Variants;

      --  Local variables

      Loop_Body : constant List_Id := Statements (Stmt);
      Scheme    : constant Opt_N_Iteration_Scheme_Id :=
        Iteration_Scheme (Stmt);
      Loop_Id   : constant E_Loop_Id := Entity (Identifier (Stmt));
      Next_Stmt : constant Node_Id := Next (Stmt);

      Loop_Stmts      : Node_Lists.List;
      Initial_Stmts   : Node_Lists.List;
      Final_Stmts     : Node_Lists.List;
      Loop_Invariants : Node_Lists.List;
      Loop_Variants   : Node_Lists.List;
      Frame_Constants : Entity_Sets.Set;
      Other_Constants : Entity_Sets.Set;

      Initial_Prog : W_Prog_Id;
      Final_Prog   : W_Prog_Id;

      --  Variables for the selected loop invariants, default initialized to
      --  the proper values when the loop does not have an invariant.

      Inv_Check : W_Prog_Id := +Void;

      --  Variable for the implicit invariant for dynamic properties of
      --  modified objects.

      Dyn_Types_Inv : W_Pred_Id := True_Pred;

      Loop_Param_Ent  : Opt_E_Loop_Parameter_Id := Empty;
      Loop_Index      : W_Identifier_Id := Why_Empty;
      Loop_Index_Type : W_Type_Id := EW_Int_Type;
      --  These three variables hold the loop parameter in Ada and Why, if any

      --  Constants specific to range quantification

      Low_Id  : W_Identifier_Id := Why_Empty;
      High_Id : W_Identifier_Id := Why_Empty;

      --  Start of processing for Transform_Loop_Statement

   begin
      --  Add the loop index to the entity table

      if Present (Scheme) and then No (Condition (Scheme)) then
         if Present (Loop_Parameter_Specification (Scheme)) then
            Loop_Param_Ent :=
              Defining_Identifier (Loop_Parameter_Specification (Scheme));

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);

            declare
               Index_Item : constant Item_Type :=
                 Mk_Item_Of_Entity (Loop_Param_Ent);
            begin
               pragma Assert (Index_Item.Kind = Regular);

               Loop_Index := Index_Item.Main.B_Name;
               Loop_Index_Type := Base_Why_Type (Get_Typ (Loop_Index));
               Insert_Item (Loop_Param_Ent, Index_Item);
            end;
         else
            pragma Assert (Present (Iterator_Specification (Scheme)));
            Loop_Param_Ent :=
              Defining_Identifier (Iterator_Specification (Scheme));

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);

            declare
               Index_Item : constant Item_Type :=
                 Mk_Item_Of_Entity (Loop_Param_Ent);
            begin
               pragma Assert (Index_Item.Kind = Regular);

               Loop_Index := Index_Item.Main.B_Name;
               Loop_Index_Type := Get_Typ (Loop_Index);
               Insert_Item (Loop_Param_Ent, Index_Item);
            end;
         end if;

         Low_Id := New_Temp_Identifier (Typ => Loop_Index_Type);
         High_Id := New_Temp_Identifier (Typ => Loop_Index_Type);
      end if;

      --  Retrieve the different parts of the loop

      Loop_Stmts := Get_Flat_Statement_And_Declaration_List (Loop_Body);
      Get_Loop_Invariant
        (Loop_Stmts          => Loop_Stmts,
         Initial_Stmts       => Initial_Stmts,
         Loop_Invariants     => Loop_Invariants,
         Loop_Variants       => Loop_Variants,
         Final_Stmts         => Final_Stmts,
         Frame_Constants     => Frame_Constants,
         Imprecise_Constants => Other_Constants);

      declare
         Why_Invariants       :
           W_Pred_Array (1 .. Integer (Loop_Invariants.Length));
         Save_Loop_Init       : constant Boolean := In_Loop_Initial_Statements
         with Ghost;
         Save_Imprecise_Const : Entity_Sets.Set := Imprecise_Constants;

      begin
         --  Transform statements before and after the loop invariants

         In_Loop_Initial_Statements := True;
         Initial_Prog :=
           Transform_Loop_Body_Statements (Initial_Stmts, Params);
         In_Loop_Initial_Statements := Save_Loop_Init;

         Save_Imprecise_Const := Imprecise_Constants;
         Imprecise_Constants.Union (Other_Constants);
         Final_Prog := Transform_Loop_Body_Statements (Final_Stmts, Params);
         Imprecise_Constants.Move (Save_Imprecise_Const);

         --  Generate the implicit invariant for the dynamic properties of
         --  objects modified in the loop.

         Dyn_Types_Inv :=
           Generate_Frame_Condition
             (Stmt,
              Low_Id          => +Low_Id,
              High_Id         => +High_Id,
              Frame_Constants => Frame_Constants);

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
                     Expr          : N_Subexpr_Id;
                     One_Inv_Check : W_Prog_Id;
                     One_Invariant : W_Pred_Id;
                     One_Message   : String_Id;
                     One_Inv_Var   : constant W_Identifier_Id :=
                       New_Temp_Identifier
                         (Typ => EW_Bool_Type, Base_Name => "inv");
                  begin
                     Transform_Pragma_Check
                       (Stmt    => Loop_Invariant,
                        Expr    => Expr,
                        Params  => Params,
                        Runtime => One_Inv_Check,
                        Pred    => One_Invariant,
                        Msg     => One_Message);

                     --  Add checking of RTE in the Nth loop invariant, and use
                     --  it to guard the checking of RTE for (N+1)th and beyond
                     --  loop invariants.

                     Inv_Check :=
                       New_Binding
                         (Name    => One_Inv_Var,
                          Def     => One_Inv_Check,
                          Context => New_Ignore (Prog => Inv_Check));

                     --  Add the predicate for the Nth loop invariant

                     Why_Invariants (Count) :=
                       New_VC_Pred
                         (Ada_Node   => Expr,
                          Expr       => One_Invariant,
                          Reason     => VC_Loop_Invariant,
                          Check_Info =>
                            New_Check_Info (User_Message => One_Message));
                     Count := Count - 1;
                  end;
               end loop;
            end;
         end if;

         --  Depending on the form of the loop, put together the generated Why
         --  nodes in a different way. [Wrap_Loop] needs to be called on every
         --  path, as it takes care or popping the stack of exit paths by
         --  calling [Exits.Wrap_Loop_Body].

         --  Case of a simple loop

         if No (Scheme) then
            return
              Wrap_Loop
                (Loop_Id            => Loop_Id,
                 Loop_Start         => Initial_Prog,
                 Loop_End           => Final_Prog,
                 Enter_Condition    => True_Prog,
                 Exit_Condition     => False_Prog,
                 Implicit_Invariant => Dyn_Types_Inv,
                 User_Invariants    => Why_Invariants,
                 Invariant_Check    => Inv_Check,
                 Variants           => Transform_Loop_Variants (Loop_Variants),
                 Variant_Check      => Check_Loop_Variants (Loop_Variants),
                 First_Stmt         => Loop_Stmts.First_Element,
                 Next_Stmt          => Next_Stmt,
                 Last_Inv           =>
                   (if Loop_Invariants.Is_Empty
                    then Empty
                    else Loop_Invariants.Last_Element),
                 Params             => Params);

         --  Case of a WHILE loop

         elsif Present (Condition (Scheme)) then
            While_Loop :
            declare
               Cond_Prog : constant W_Prog_Id :=
                 +Transform_Expr_With_Actions
                    (Condition (Scheme),
                     Condition_Actions (Scheme),
                     EW_Bool_Type,
                     EW_Prog,
                     Params => Params);
               Cond_Pred : constant W_Pred_Id :=
                 +Transform_Expr_With_Actions
                    (Condition (Scheme),
                     Condition_Actions (Scheme),
                     EW_Bool_Type,
                     EW_Pred,
                     Params => Params);

               --  If the Loop_Assertion pragma comes first in the loop body
               --  (possibly inside nested block statements), then we can use
               --  the loop condition as an implicit invariant of the generated
               --  Why loop. In other cases, we cannot, as this would not be
               --  always correct.

               Impl_Pred : constant W_Pred_Id :=
                 (if Is_Essentially_Void (Initial_Prog)
                  then Cond_Pred
                  else True_Pred);

               Impl_Inv : constant W_Pred_Id :=
                 +New_And_Expr
                    (Left   => +Dyn_Types_Inv,
                     Right  => +Impl_Pred,
                     Domain => EW_Prog);
            begin
               return
                 Wrap_Loop
                   (Loop_Id            => Loop_Id,
                    Loop_Start         => Initial_Prog,
                    Loop_End           => Final_Prog,
                    Enter_Condition    => Cond_Prog,
                    Exit_Condition     =>
                      +W_Not_OId'
                        (New_Not
                           (Ada_Node => Condition (Scheme),
                            Domain   => EW_Prog,
                            Right    => +Cond_Prog)),
                    Implicit_Invariant => Impl_Inv,
                    User_Invariants    => Why_Invariants,
                    Invariant_Check    => Inv_Check,
                    Variants           =>
                      Transform_Loop_Variants (Loop_Variants),
                    Variant_Check      => Check_Loop_Variants (Loop_Variants),
                    First_Stmt         => Loop_Stmts.First_Element,
                    Next_Stmt          => Next_Stmt,
                    Last_Inv           =>
                      (if Loop_Invariants.Is_Empty
                       then Empty
                       else Loop_Invariants.Last_Element),
                    Params             => Params);
            end While_Loop;

         --  Case of a FOR loop

         --  Here, we set the condition to express that the index is in the
         --  range of the loop. We need to evaluate the range expression
         --  once at the beginning of the loop, to get potential checks
         --  in that expression only once.

         else
            pragma Assert (Present (Loop_Index));

            For_Loop :
            declare
               Over_Range : constant Boolean :=
                 Present (Loop_Parameter_Specification (Scheme));
               --  For loops my iterate either on a range or on an iterator.

               LParam_Spec : constant Node_Id :=
                 (if Over_Range
                  then Loop_Parameter_Specification (Scheme)
                  else Iterator_Specification (Scheme));
               Over_Node   : constant Node_Id :=
                 (if Over_Range
                  then Discrete_Subtype_Definition (LParam_Spec)
                  else Get_Container_In_Iterator_Specification (LParam_Spec));
               Index_Deref : constant W_Prog_Id :=
                 New_Deref
                   (Ada_Node => Stmt,
                    Right    => +Loop_Index,
                    Typ      => Loop_Index_Type);

               --  Constants specific to iterator specification

               Typ_For_Cont  : constant W_Type_Id :=
                 (if Over_Range
                  then EW_Int_Type
                  else
                    Type_Of_Node
                      (Etype
                         (First_Formal
                            (Get_Iterable_Type_Primitive
                               (Etype (Over_Node), Name_First)))));
               W_Container   : constant W_Expr_Id :=
                 (if Over_Range
                  then Why_Empty
                  else
                    New_Temp_For_Expr
                      (Insert_Simple_Conversion
                         (Domain => EW_Prog,
                          Expr   =>
                            Transform_Expr (Over_Node, EW_Prog, Params),
                          To     => Typ_For_Cont),
                       Need_Temp => not SPARK_Atree.Is_Variable (Over_Node)));
               --  Introduce a temporary variable for the container expression
               --  except if it is a variable.
               W_Container_T : constant W_Expr_Id :=
                 (if Over_Range
                  then Why_Empty
                  elsif SPARK_Atree.Is_Variable (Over_Node)
                  then
                    Insert_Simple_Conversion
                      (Domain => EW_Term,
                       Expr   => Transform_Expr (Over_Node, EW_Term, Params),
                       To     => Typ_For_Cont)
                  else W_Container);
               --  Container expression in the term domain

               --  For for of loops, we need an identifier for the additional
               --  variable holding the iterator.

               Need_Iter    : constant Boolean :=
                 not Over_Range and then Of_Present (LParam_Spec);
               Typ_For_Iter : constant W_Type_Id :=
                 (if Need_Iter
                  then
                    Type_Of_Node
                      (Get_Iterable_Type_Primitive
                         (Typ => Etype (Over_Node), Nam => Name_First))
                  else Loop_Index_Type);
               Nam_For_Iter : constant W_Identifier_Id :=
                 (if not Need_Iter
                  then Loop_Index
                  else
                    New_Temp_Identifier
                      (Ada_Node => Empty, Typ => Typ_For_Iter));
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
               with Pre => Domain in EW_Prog | EW_Pred and then not Over_Range;
               --  @param Domain in which the constraint should be created
               --  @result Has_Element (W_Container, Iter_Deref)

               function Exit_Condition_For_Iterable return W_Expr_Id
               with Pre => not Over_Range;
               --  @result not (Has_Element (W_Container, Next (Iter_Deref)))

               function Init_Iter return W_Prog_Id
               with Pre => not Over_Range;
               --  @result First (W_Container)

               function Loop_Index_Value (Domain : EW_Domain) return W_Expr_Id
               with
                 Pre =>
                   Domain in EW_Prog | EW_Term
                   and then not Over_Range
                   and then Of_Present (LParam_Spec);
               --  @result Element (W_Container, Iter_Deref)

               function Update_Index return W_Prog_Id
               with Pre => not Over_Range and then Of_Present (LParam_Spec);
               --  @result if Has_Element (W_Container, Iter_Deref)
               --       then Loop_Index := Element (W_Container, Iter_Deref)

               -----------------------------
               -- Constraint_For_Iterable --
               -----------------------------

               function Constraint_For_Iterable
                 (Domain : EW_Domain) return W_Expr_Id
               is
                  H_Elmt   : constant E_Function_Id :=
                    Get_Iterable_Type_Primitive
                      (Etype (Over_Node), Name_Has_Element);
                  W_H_Elmt : constant W_Identifier_Id :=
                    +Transform_Identifier
                       (Params => Params,
                        Expr   => H_Elmt,
                        Ent    => H_Elmt,
                        Domain => Domain);
                  Cur_Expr : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain => EW_Term,
                       Expr   => +Iter_Deref,
                       To     => Typ_For_Iter);
                  Check    : constant Boolean := Domain = EW_Prog;
               begin
                  pragma Assert (W_Container_T /= Why_Empty);
                  return
                    +New_Function_Call
                       (Ada_Node => LParam_Spec,
                        Subp     => H_Elmt,
                        Name     => W_H_Elmt,
                        Args     =>
                          (1 => (if Check then W_Container else W_Container_T),
                           2 => Cur_Expr),
                        Domain   => Domain,
                        Check    => Check,
                        Typ      => EW_Bool_Type);
               end Constraint_For_Iterable;

               ---------------------------------
               -- Exit_Condition_For_Iterable --
               ---------------------------------

               function Exit_Condition_For_Iterable return W_Expr_Id is
                  H_Elmt   : constant E_Function_Id :=
                    Get_Iterable_Type_Primitive
                      (Etype (Over_Node), Name_Has_Element);
                  W_H_Elmt : constant W_Identifier_Id :=
                    +Transform_Identifier
                       (Params => Params,
                        Expr   => H_Elmt,
                        Ent    => H_Elmt,
                        Domain => EW_Prog);
                  N_Elmt   : constant E_Function_Id :=
                    Get_Iterable_Type_Primitive (Etype (Over_Node), Name_Next);
                  W_N_Elmt : constant W_Identifier_Id :=
                    +Transform_Identifier
                       (Params => Params,
                        Expr   => N_Elmt,
                        Ent    => N_Elmt,
                        Domain => EW_Prog);
                  Cur_Expr : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain => EW_Term,
                       Expr   => +Iter_Deref,
                       To     => Typ_For_Iter);
               begin
                  pragma Assert (W_Container /= Why_Empty);
                  return
                    +W_Not_Id'
                      (New_Not
                         (Ada_Node => LParam_Spec,
                          Domain   => EW_Prog,
                          Right    =>
                            +New_VC_Call
                               (Ada_Node => LParam_Spec,
                                Name     => W_H_Elmt,
                                Progs    =>
                                  (1 => W_Container,
                                   2 =>
                                     +New_VC_Call
                                        (Ada_Node => LParam_Spec,
                                         Name     => W_N_Elmt,
                                         Progs    =>
                                           (1 => W_Container, 2 => Cur_Expr),
                                         Reason   => VC_Precondition,
                                         Typ      => EW_Bool_Type)),
                                Reason   => VC_Precondition,
                                Typ      => EW_Bool_Type)));
               end Exit_Condition_For_Iterable;

               ---------------
               -- Init_Iter --
               ---------------

               function Init_Iter return W_Prog_Id is
                  First : constant E_Function_Id :=
                    Get_Iterable_Type_Primitive
                      (Etype (Over_Node), Name_First);

                  pragma Assert (W_Container /= Why_Empty);

                  Call_First : constant W_Expr_Id :=
                    +New_VC_Call
                       (Ada_Node => LParam_Spec,
                        Name     =>
                          W_Identifier_Id
                            (Transform_Identifier
                               (Params => Params,
                                Expr   => First,
                                Ent    => First,
                                Domain => EW_Prog)),
                        Progs    => (1 => W_Container),
                        Reason   => VC_Precondition,
                        Typ      => Typ_For_Iter);
               begin
                  return +Call_First;
               end Init_Iter;

               ----------------------
               -- Loop_Index_Value --
               ----------------------

               function Loop_Index_Value (Domain : EW_Domain) return W_Expr_Id
               is
                  Elmt     : constant E_Function_Id :=
                    Get_Iterable_Type_Primitive
                      (Etype (Over_Node), Name_Element);
                  Cur_Expr : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain => EW_Term,
                       Expr   => +Iter_Deref,
                       To     => Typ_For_Iter);
                  W_Elmt   : constant W_Identifier_Id :=
                    +Transform_Identifier
                       (Params => Params,
                        Expr   => Elmt,
                        Ent    => Elmt,
                        Domain => Domain);
                  Check    : constant Boolean := Domain = EW_Prog;
               begin
                  pragma Assert (W_Container /= Why_Empty);
                  return
                    New_Function_Call
                      (Ada_Node => LParam_Spec,
                       Subp     => Elmt,
                       Name     => W_Elmt,
                       Args     =>
                         (1 => (if Check then W_Container else W_Container_T),
                          2 => Cur_Expr),
                       Domain   => Domain,
                       Check    => Check,
                       Typ      => Type_Of_Node (Etype (Elmt)));
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
                       Condition => Constraint_For_Iterable (EW_Prog),
                       Then_Part =>
                         New_Assignment
                           (Ada_Node => Stmt,
                            Name     => Loop_Index,
                            Labels   => Symbol_Sets.Empty_Set,
                            Value    =>
                              +Insert_Simple_Conversion
                                 (Domain => EW_Term,
                                  Expr   => +Call_Elmt,
                                  To     => Loop_Index_Type),
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

               function Skip_Empty_Iterations return W_Prog_Id
               with
                 Pre =>
                   Over_Range and then Present (Iterator_Filter (LParam_Spec));
               --  Skip iterations of the loop until the filter condition
               --  holds. If we reach the end of the loop, we exit.

               --------------------
               -- Construct_Cond --
               --------------------

               function Construct_Cond return W_Prog_Id is
               begin
                  if Over_Range then

                     --  Low_Id <= Index_Deref <= High_Id

                     return
                       +New_Range_Expr
                          (Domain => EW_Prog,
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
                          (if Why_Type_Is_BitVector (Loop_Index_Type)
                           then MF_BVs (Loop_Index_Type).Prog_Eq
                           else Why_Eq);
                        Exit_Cond  : constant W_Expr_Id :=
                          New_Call
                            (Domain => EW_Prog,
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
                        return
                          New_Assignment
                            (Name   => Loop_Index,
                             Value  => +Init_Index,
                             Labels => Symbol_Sets.Empty_Set,
                             Typ    => Loop_Index_Type);
                     end;
                  else
                     if Need_Iter then

                        --  if Has_Element (W_Container, Iter_Deref) then
                        --    Loop_Index := Element (W_Container, Iter_Deref)

                        return Update_Index;
                     else

                        --  Loop_Index := First (W_Container)

                        return
                          New_Assignment
                            (Name   => Nam_For_Iter,
                             Value  => Init_Iter,
                             Labels => Symbol_Sets.Empty_Set,
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
                       +Range_Expr
                          (Over_Node,
                           New_Deref
                             (Right => Loop_Index, Typ => Loop_Index_Type),
                           EW_Pred,
                           Params => Params,
                           T_Type => Loop_Index_Type);

                  else
                     declare
                        Cursor_Inv : constant W_Pred_Id :=
                          New_And_Pred
                            (Left  =>
                               Compute_Dynamic_Inv_And_Initialization
                                 (Expr   => +Iter_Deref,
                                  Ty     =>
                                    Etype
                                      (Get_Iterable_Type_Primitive
                                         (Typ => Etype (Over_Node),
                                          Nam => Name_First)),
                                  Params => Params),
                             Right => +Constraint_For_Iterable (EW_Pred));
                        --  Dynamic_Invariant (Iter_Deref)
                        --  and Has_Element (W_Container, Iter_Deref)

                     begin
                        --  If we are in a "for of" iteration, add:
                        --    Index_Deref = Element (W_Container, Iter_Deref)

                        if Need_Iter then
                           declare
                              Elmt_Iter : constant W_Pred_Id :=
                                New_Comparison
                                  (Why_Eq,
                                   +Index_Deref,
                                   +Loop_Index_Value (EW_Term));
                           begin
                              return New_And_Pred (Cursor_Inv, Elmt_Iter);
                           end;
                        else
                           return Cursor_Inv;
                        end if;
                     end;
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
                          (if Why_Type_Is_BitVector (Loop_Index_Type)
                           then
                             (if Is_Reverse
                              then MF_BVs (Loop_Index_Type).Sub
                              else MF_BVs (Loop_Index_Type).Add)
                           else
                             (if Is_Reverse
                              then Int_Infix_Subtr
                              else Int_Infix_Add));
                        One_Expr    : constant W_Expr_Id :=
                          (if Why_Type_Is_BitVector (Loop_Index_Type)
                           then
                             New_Modular_Constant
                               (Ada_Node => Stmt,
                                Value    => Uint_1,
                                Typ      => Loop_Index_Type)
                           else
                             New_Integer_Constant
                               (Ada_Node => Stmt, Value => Uint_1));
                        Update_Expr : constant W_Prog_Id :=
                          New_Call
                            (Ada_Node => Stmt,
                             Name     => Update_Op,
                             Args     => (1 => +Index_Deref, 2 => +One_Expr),
                             Typ      => Loop_Index_Type);
                     begin
                        return
                          New_Assignment
                            (Ada_Node => Stmt,
                             Name     => Loop_Index,
                             Labels   => Symbol_Sets.Empty_Set,
                             Value    => +Update_Expr,
                             Typ      => Loop_Index_Type);
                     end;
                  else
                     declare
                        Next      : constant E_Function_Id :=
                          Get_Iterable_Type_Primitive
                            (Etype (Over_Node), Name_Next);
                        Cur_Expr  : constant W_Expr_Id :=
                          Insert_Simple_Conversion
                            (Domain => EW_Term,
                             Expr   => +Iter_Deref,
                             To     => Typ_For_Iter);
                        Call_Next : constant W_Expr_Id :=
                          +New_VC_Call
                             (Ada_Node => LParam_Spec,
                              Name     =>
                                W_Identifier_Id
                                  (Transform_Identifier
                                     (Params => Params,
                                      Expr   => Next,
                                      Ent    => Next,
                                      Domain => EW_Prog)),
                              Progs    => (1 => W_Container, 2 => Cur_Expr),
                              Reason   => VC_Precondition,
                              Typ      => Typ_For_Iter);
                        Upd_Next  : constant W_Prog_Id :=
                          New_Assignment
                            (Ada_Node => Stmt,
                             Name     => Nam_For_Iter,
                             Labels   => Symbol_Sets.Empty_Set,
                             Value    =>
                               +Insert_Simple_Conversion
                                  (Domain => EW_Term,
                                   Expr   => +Call_Next,
                                   To     => Get_Type (+Iter_Deref)),
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

               ----------------------------
               -- Skip_Empty_Iterations  --
               ----------------------------

               function Skip_Empty_Iterations return W_Prog_Id is
                  --  Inside for loops containing iterator filters, the loop
                  --  invariant only holds for iterations that are enabled.
                  --  To match the Why3 semantics of loop invariants, we need
                  --  to skip disabled iterations. Intuitively, the generated
                  --  code is a loop over disabled iterations. We do not
                  --  actually generate the loop though but rather simulate
                  --  it by havocking the index parameter. For a loop:
                  --
                  --    for I in Low .. High when Cond loop ...
                  --
                  --  We generate:
                  --
                  --    let old_index = !i in
                  --    any unit
                  --      writes { i }
                  --      ensures { old !i <= !i <= high
                  --           /\ (forall tmp. old !i <= tmp < !i -> not cond)
                  --           /\ (cond \/ !i = high) };
                  --    ignore { let tmp = any int
                  --               ensures { old_index <= result < !i } in
                  --             cond };
                  --    if not cond then raise loop_exit;

                  Filter     : constant Node_Id :=
                    Iterator_Filter (LParam_Spec);
                  Is_Reverse : constant Boolean :=
                    Reverse_Present (LParam_Spec);
                  Exit_Index : constant W_Expr_Id :=
                    (if Is_Reverse then +Low_Id else +High_Id);
                  Exit_Cond  : constant W_Pred_Id :=
                    New_Call
                      (Name => Why_Eq,
                       Typ  => EW_Bool_Type,
                       Args => (+Index_Deref, +Exit_Index));
                  --  !i = high or !i = low

                  Range_Expr : constant W_Pred_Id :=
                    +New_Range_Expr
                       (Domain => EW_Pred,
                        Low    =>
                          (if Is_Reverse
                           then +Low_Id
                           else
                             New_Old
                               (Expr => +Index_Deref, Domain => EW_Term)),
                        High   =>
                          (if not Is_Reverse
                           then +High_Id
                           else
                             New_Old
                               (Expr => +Index_Deref, Domain => EW_Term)),
                        Expr   => +Index_Deref);
                  --  old !i <= !i <= high or low <= !i <= old !i

                  Old_Index   : constant W_Identifier_Id :=
                    New_Temp_Identifier
                      (Typ => Loop_Index_Type, Base_Name => "old_index");
                  Index_Tmp   : constant W_Identifier_Id :=
                    New_Temp_Identifier
                      (Typ => Loop_Index_Type, Base_Name => "index");
                  Strict_Comp : constant W_Identifier_Id :=
                    (if Is_Reverse and Why_Type_Is_BitVector (Loop_Index_Type)
                     then MF_BVs (Loop_Index_Type).Ugt
                     elsif Is_Reverse
                     then Int_Infix_Gt
                     elsif Why_Type_Is_BitVector (Loop_Index_Type)
                     then MF_BVs (Loop_Index_Type).Ult
                     else Int_Infix_Lt);
                  Large_Comp  : constant W_Identifier_Id :=
                    (if Is_Reverse and Why_Type_Is_BitVector (Loop_Index_Type)
                     then MF_BVs (Loop_Index_Type).Uge
                     elsif Is_Reverse
                     then Int_Infix_Ge
                     elsif Why_Type_Is_BitVector (Loop_Index_Type)
                     then MF_BVs (Loop_Index_Type).Ule
                     else Int_Infix_Le);
                  Tmp_Range   : constant W_Pred_Id :=
                    +New_And_Expr
                       (Left   =>
                          New_Comparison
                            (Symbol => Large_Comp,
                             Left   =>
                               New_Old
                                 (Expr => +Index_Deref, Domain => EW_Term),
                             Right  => +Index_Tmp,
                             Domain => EW_Pred),
                        Right  =>
                          New_Comparison
                            (Symbol => Strict_Comp,
                             Left   => +Index_Tmp,
                             Right  => +Index_Deref,
                             Domain => EW_Pred),
                        Domain => EW_Pred);
                  --  old !i <= tmp < i or old !i >= tmp > i

                  Last_Filter : constant W_Pred_Id :=
                    Transform_Pred (Filter, Params);
                  Exit_Stmt   : constant W_Prog_Id :=
                    New_Conditional
                      (Condition =>
                         New_Not
                           (Right =>
                              Transform_Prog (Filter, EW_Bool_Type, Params)),
                       Then_Part =>
                         New_Raise
                           (Name =>
                              Loop_Exception_Name
                                (Loop_Id, Is_Continue => False)));
                  --  if not cond then raise loop_exit;

                  Other_Filter : W_Pred_Id;
                  Check_Filter : W_Prog_Id;

               begin
                  --  When referring to skipped iterations, occurrences of I
                  --  in Cond must be translating as tmp. It happens in the
                  --  universally quantified formula occuring in the post of
                  --  the havoc program, and in the ignore block generating
                  --  checks for Cond.

                  Ada_Ent_To_Why.Push_Scope (Symbol_Table);
                  Insert_Tmp_Item_For_Entity
                    (E => Loop_Param_Ent, Name => Index_Tmp);

                  --  Compute:
                  --    (forall tmp. old !i <= tmp < !i -> not cond)

                  Other_Filter :=
                    New_Universal_Quantif
                      (Binders =>
                         (1 =>
                            New_Binder
                              (Domain   => EW_Pred,
                               Name     => Index_Tmp,
                               Arg_Type => Loop_Index_Type)),
                       Labels  => Symbol_Sets.Empty_Set,
                       Pred    =>
                         New_Conditional
                           (Condition => Tmp_Range,
                            Then_Part =>
                              New_Not
                                (Right => Transform_Pred (Filter, Params))));

                  --  Compute:
                  --    ignore { let tmp = any int
                  --               ensures { old_index <= result < !i } in
                  --             cond };

                  Check_Filter :=
                    New_Ignore
                      (Prog =>
                         New_Binding
                           (Name    => Index_Tmp,
                            Def     =>
                              New_Any_Expr
                                (Return_Type => Loop_Index_Type,
                                 Labels      => Symbol_Sets.Empty_Set,
                                 Post        =>
                                   +New_And_Expr
                                      (Left   =>
                                         New_Comparison
                                           (Symbol => Large_Comp,
                                            Left   => +Old_Index,
                                            Right  =>
                                              +New_Result_Ident
                                                 (Loop_Index_Type),
                                            Domain => EW_Pred),
                                       Right  =>
                                         New_Comparison
                                           (Symbol => Strict_Comp,
                                            Left   =>
                                              +New_Result_Ident
                                                 (Loop_Index_Type),
                                            Right  => +Index_Deref,
                                            Domain => EW_Pred),
                                       Domain => EW_Pred)),
                            Context => Transform_Prog (Filter, Params),
                            Typ     => EW_Bool_Type));
                  Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

                  --  Piece everything together

                  return
                    Sequence
                      (Left  =>
                         New_Comment
                           (Comment => NID ("Skip filtered out iterations")),
                       Right =>
                         New_Binding
                           (Name    => Old_Index,
                            Def     => +Index_Deref,
                            Context =>
                              +Sequence
                                 ((1 =>
                                     New_Any_Expr
                                       (Effects     =>
                                          New_Effects
                                            (Writes => (1 => Loop_Index)),
                                        Post        =>
                                          New_And_Pred
                                            (Conjuncts =>
                                               (1 => Range_Expr,
                                                2 => Other_Filter,
                                                3 =>
                                                  New_Or_Pred
                                                    (Left  => Exit_Cond,
                                                     Right => Last_Filter))),
                                        Return_Type => EW_Unit_Type,
                                        Labels      => Symbol_Sets.Empty_Set),
                                   2 => Check_Filter,
                                   3 => Exit_Stmt))));
               end Skip_Empty_Iterations;

               ---------------------
               -- Local Variables --
               ---------------------

               Index_Inv   : constant W_Pred_Id := Construct_Inv_For_Index;
               Cond_Prog   : constant W_Prog_Id := Construct_Cond;
               Update_Stmt : constant W_Prog_Id :=
                 +Insert_Cnt_Loc_Label (Stmt, +Construct_Update_Stmt);
               Exit_Cond   : constant W_Prog_Id := Construct_Exit_Cond;
               Impl_Inv    : W_Pred_Id :=
                 +New_And_Expr
                    (Left   => +Dyn_Types_Inv,
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
                    Warning_Status (Warn_Info_Unrolling_Inlining) = WS_Enabled
                    and then not Gnat2Why_Args.No_Loop_Unrolling,
                  Result      => Unroll,
                  Low_Val     => Low_Val,
                  High_Val    => High_Val);

               if not Gnat2Why_Args.No_Loop_Unrolling
                 and then Unroll /= No_Unrolling
               then
                  --  If the loop has an iterator filter, we need to add
                  --  the filtering expression as a guard for each loop
                  --  unrolling.

                  if Present (Iterator_Filter (LParam_Spec)) then
                     Final_Prog :=
                       New_Conditional
                         (Condition =>
                            Transform_Prog
                              (Expr          => Iterator_Filter (LParam_Spec),
                               Expected_Type => EW_Bool_Type,
                               Params        => Params),
                          Then_Part => Final_Prog);
                  end if;

                  declare
                     Inlined_Body : constant W_Prog_Id :=
                       (if Unroll = Unrolling_With_Condition
                        then
                          New_Conditional
                            (Condition => +Cond_Prog, Then_Part => +Final_Prog)
                        else Final_Prog);
                  begin
                     Entire_Loop :=
                       Unroll_Loop
                         (Loop_Id         => Loop_Id,
                          Loop_Index      => Loop_Index,
                          Loop_Index_Type => Loop_Index_Type,
                          Low_Val         => Low_Val,
                          High_Val        => High_Val,
                          Reversed        => Reverse_Present (LParam_Spec),
                          Body_Prog       => Inlined_Body,
                          Params          => Params);
                  end;

               --  Regular case of a FOR loop with a loop (in)variant, or no
               --  static bounds, requiring a proof by induction.

               else
                  --  If the loop has an iterator filter, add a statement at
                  --  the begining of the loop to skip iterations which are
                  --  filtered out. We cannot simply wrap the loop body inside
                  --  a conditionnal like for unrolled loops because the loop
                  --  invariant is only supposed to hold on enabled iterations.

                  if Present (Iterator_Filter (LParam_Spec)) then

                     --  If the Loop_Assertion pragma comes first in the loop
                     --  body (possibly inside nested block statements), then
                     --  we can use the filter expression as an implicit
                     --  invariant of the generated Why loop. In other cases,
                     --  we cannot, as this would not be always correct.

                     if Is_Essentially_Void (Initial_Prog) then
                        Impl_Inv :=
                          +New_And_Expr
                             (Left   => +Impl_Inv,
                              Right  =>
                                +Transform_Expr
                                   (Expr   => Iterator_Filter (LParam_Spec),
                                    Domain => EW_Pred,
                                    Params => Params),
                              Domain => EW_Prog);
                     end if;

                     Prepend (Skip_Empty_Iterations, Initial_Prog);
                  end if;

                  Entire_Loop :=
                    Wrap_Loop
                      (Loop_Id            => Loop_Id,
                       Loop_Start         => Initial_Prog,
                       Loop_End           => Final_Prog,
                       Enter_Condition    => Cond_Prog,
                       Exit_Condition     => Exit_Cond,
                       Implicit_Invariant => Impl_Inv,
                       User_Invariants    => Why_Invariants,
                       Invariant_Check    => Inv_Check,
                       Variants           =>
                         Transform_Loop_Variants (Loop_Variants),
                       Variant_Check      =>
                         Check_Loop_Variants (Loop_Variants),
                       Update_Stmt        => Update_Stmt,
                       First_Stmt         => Loop_Stmts.First_Element,
                       Next_Stmt          => Next_Stmt,
                       Last_Inv           =>
                         (if Loop_Invariants.Is_Empty
                          then Empty
                          else Loop_Invariants.Last_Element),
                       Params             => Params);

                  Prepend (Construct_Init_Prog, Entire_Loop);
               end if;

               --  Create new variable for iterator if needed

               if Need_Iter then
                  Entire_Loop :=
                    New_Binding_Ref
                      (Name    => Nam_For_Iter,
                       Def     => Init_Iter,
                       Context => Entire_Loop,
                       Typ     => EW_Unit_Type);
               end if;

               --  Bind the temporary variable used for the container
               --  expression if any.

               if W_Container /= Why_Empty then
                  Entire_Loop :=
                    +Binding_For_Temp
                       (Ada_Node => Loop_Id,
                        Domain   => EW_Prog,
                        Tmp      => W_Container,
                        Context  => +Entire_Loop);
               end if;

               --  Add let bindings for bounds

               if Over_Range then
                  declare
                     Actual_Range : constant Node_Id := Get_Range (Over_Node);
                     High_Expr    : constant W_Prog_Id :=
                       Transform_Prog
                         (High_Bound (Actual_Range),
                          Loop_Index_Type,
                          Params => Params);
                     Low_Expr     : constant W_Prog_Id :=
                       Transform_Prog
                         (Low_Bound (Actual_Range),
                          Loop_Index_Type,
                          Params => Params);
                  begin
                     --  Insert assignment to high bound first, so that
                     --  assignment to low bound is done prior to assignment to
                     --  high bound in generated Why3 code. This ensures that a
                     --  common error is detected on low bound rather than high
                     --  bound, which is more intuitive.

                     Entire_Loop :=
                       New_Typed_Binding
                         (Stmt, High_Id, High_Expr, Entire_Loop);
                     Entire_Loop :=
                       New_Typed_Binding (Stmt, Low_Id, Low_Expr, Entire_Loop);
                  end;
               end if;

               --  For loop_parameter_specification whose
               --  discrete_subtype_definition is a subtype_indication,
               --  we generate a check that the range_constraint of the
               --  subtype_indication is compatible with the given subtype.

               if Nkind (Over_Node) = N_Subtype_Indication then
                  Prepend
                    (Check_Subtype_Indication
                       (Params   => Params,
                        N        => Over_Node,
                        Sub_Type => Etype (Defining_Identifier (LParam_Spec))),
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

   function Transform_Loop_Variant
     (Stmt : N_Pragma_Id; Params : Transformation_Params) return W_Variants_Id
   is
      Variant       : Opt_N_Pragma_Argument_Association_Id;
      Count         : Natural := 0;
      Assert_Params : constant Transformation_Params :=
        (Params with delta Phase => Generate_VCs_For_Assert);
   begin
      --  Count Variant items in the Loop_Variant pragma

      Variant := First (Pragma_Argument_Associations (Stmt));

      while Present (Variant) loop
         Count := Count + 1;
         Next (Variant);
      end loop;

      Variant := First (Pragma_Argument_Associations (Stmt));
      declare
         Variants : W_Variant_Array (1 .. Count);
      begin
         for I in Variants'Range loop
            declare
               Expr : constant N_Subexpr_Id := Expression (Variant);
               WTyp : constant W_Type_Id := Base_Why_Type_No_Bool (Expr);
               Cmp  : constant W_Identifier_Id :=
                 (if Chars (Variant) = Name_Decreases
                  then
                    (if Why_Type_Is_BitVector (WTyp)
                     then MF_BVs (WTyp).Ult
                     else Int_Infix_Lt)
                  else
                    (if Why_Type_Is_BitVector (WTyp)
                     then MF_BVs (WTyp).Ugt
                     else Int_Infix_Gt));
            begin
               --  We delegate the creation of the assertion to Why3, so we
               --  pass the labels used for the VC in an extra Labels node in
               --  the tree.

               Variants (I) :=
                 New_Variant
                   (Cmp_Op => Cmp,
                    Labels =>
                      New_VC_Labels
                        (Variant,
                         Reason     => VC_Loop_Variant,
                         Check_Info => New_Check_Info),
                    Expr   =>
                      +Transform_Expr
                         (Expr          => Expr,
                          Expected_Type => WTyp,
                          Domain        => EW_Pterm,
                          Params        => Assert_Params));
            end;

            Next (Variant);
         end loop;

         return New_Variants (Variants => Variants);
      end;
   end Transform_Loop_Variant;

   -----------------
   -- Unroll_Loop --
   -----------------

   function Unroll_Loop
     (Loop_Id         : E_Loop_Id;
      Loop_Index      : W_Identifier_Id;
      Loop_Index_Type : W_Type_Id;
      Low_Val         : Uint;
      High_Val        : Uint;
      Reversed        : Boolean;
      Body_Prog       : W_Prog_Id;
      Params          : Transformation_Params) return W_Prog_Id
   is
      function Repeat_Loop (Loop_Body : W_Prog_Id) return W_Prog_Id;
      --  Repeat the loop body for each value of the index

      -----------------
      -- Repeat_Loop --
      -----------------

      function Repeat_Loop (Loop_Body : W_Prog_Id) return W_Prog_Id is
         First_Val : constant Uint := (if Reversed then High_Val else Low_Val);
         Last_Val  : constant Uint := (if Reversed then Low_Val else High_Val);
         Cur_Val   : Uint;
         Cur_Cst   : W_Prog_Id;

         Stmt_List :
           W_Prog_Array
             (1
              .. 2
                 * (Integer (UI_To_Int (High_Val) - UI_To_Int (Low_Val) + 1)));
         Cur_Idx   : Positive;

      begin
         Cur_Val := First_Val;
         Cur_Idx := 1;
         loop
            Cur_Cst :=
              (if Why_Type_Is_BitVector (Loop_Index_Type)
               then
                 New_Modular_Constant
                   (Value => Cur_Val, Typ => Loop_Index_Type)
               else New_Integer_Constant (Value => Cur_Val));
            Stmt_List (Cur_Idx) :=
              New_Assignment
                (Name   => Loop_Index,
                 Value  => Cur_Cst,
                 Labels => Symbol_Sets.Empty_Set,
                 Typ    => Loop_Index_Type);
            Cur_Idx := Cur_Idx + 1;
            Stmt_List (Cur_Idx) := Loop_Body;
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

      Exit_Ident : constant W_Name_Id :=
        Loop_Exception_Name (Loop_Id, Is_Continue => False);
      Cont_Ident : constant W_Name_Id :=
        Loop_Exception_Name (Loop_Id, Is_Continue => True);
      Loop_Body  : constant W_Prog_Id :=
        New_Try_Block
          (Prog    => Body_Prog,
           Handler => (1 => New_Handler (Name => Cont_Ident, Def => +Void)));

      Try_Body : W_Prog_Id :=
        Bind_From_Mapping_In_Prog
          (Params => Params,
           Map    => Map_For_Loop_Entry (Loop_Id),
           Expr   =>
             Sequence
               (New_Comment
                  (Comment =>
                     NID
                       ("Unrolling of the loop statements"
                        & (if Sloc (Loop_Id) > 0
                           then
                             " of loop "
                             & Build_Location_String (Sloc (Loop_Id))
                           else ""))),
                Repeat_Loop (Loop_Body)));

   begin
      Try_Body :=
        New_Try_Block
          (Prog    => Try_Body,
           Handler => (1 => New_Handler (Name => Exit_Ident, Def => +Void)));

      return
        Sequence
          (New_Comment
             (Comment =>
                NID
                  ("Translation of an unrolled Ada loop"
                   & (if Sloc (Loop_Id) > 0
                      then " from " & Build_Location_String (Sloc (Loop_Id))
                      else ""))),
           Try_Body);
   end Unroll_Loop;

   ---------------
   -- Wrap_Loop --
   ---------------

   --  Generate the following loop expression:
   --
   --  if enter_condition then
   --    try
   --      let loop_entry_tmps = saved_values in
   --      let variant_tmps = ref 0 in
   --      loop
   --        code_before {
   --          loop_start;
   --          invariant_check;
   --        }
   --        invariant { user_invariant }
   --        variants { user_variants }
   --        code_after {
   --          assume { implicit_invariant };
   --          try
   --            loop_end;
   --          with loop_continue -> void
   --          if exit_condition then
   --            raise loop_name;
   --          [Update_Stmt;]
   --        }
   --      end loop
   --    with loop_exit -> void
   --  end if

   function Wrap_Loop
     (Loop_Id            : E_Loop_Id;
      Loop_Start         : W_Prog_Id;
      Loop_End           : W_Prog_Id;
      Enter_Condition    : W_Prog_Id;
      Exit_Condition     : W_Prog_Id;
      Implicit_Invariant : W_Pred_Id;
      User_Invariants    : W_Pred_Array;
      Invariant_Check    : W_Prog_Id;
      Variants           : W_Variants_Array;
      Variant_Check      : W_Prog_Id;
      Update_Stmt        : W_Prog_Id := Why_Empty;
      First_Stmt         : Node_Id;
      Next_Stmt          : Node_Id := Empty;
      Last_Inv           : Opt_N_Pragma_Id := Empty;
      Params             : Transformation_Params) return W_Prog_Id
   is
      Exit_Ident  : constant W_Name_Id :=
        Loop_Exception_Name (Loop_Id, Is_Continue => False);
      Cont_Ident  : constant W_Name_Id :=
        Loop_Exception_Name (Loop_Id, Is_Continue => True);
      Loop_Before : constant W_Prog_Id :=
        Sequence
          ((1 => Loop_Start,
            2 =>
              New_Comment
                (Comment =>
                   NID
                     ("Check for absence of RTE in the loop"
                      & " invariant and variant")),
            3 => Invariant_Check,
            4 => Variant_Check));
      Loop_After  : constant W_Prog_Id :=
        Sequence
          ((1 =>
              New_Comment
                (Comment =>
                   NID
                     ("Assume implicit invariants from the loop"
                      & (if Sloc (Loop_Id) > 0
                         then " " & Build_Location_String (Sloc (Loop_Id))
                         else ""))),
            2 => New_Assume_Statement (Pred => Implicit_Invariant),
            3 =>
              New_Comment
                (Comment =>
                   NID
                     ("Continuation of loop after loop"
                      & " invariant and variant")),
            4 =>
              New_Try_Block
                (Prog    => Loop_End,
                 Handler =>
                   (1 => New_Handler (Name => Cont_Ident, Def => +Void))),
            5 =>
              New_Comment
                (Comment =>
                   NID
                     ("Check for the exit condition and loop"
                      & " statements appearing before the loop invariant"
                      & (if Sloc (Loop_Id) > 0
                         then
                           " of loop " & Build_Location_String (Sloc (Loop_Id))
                         else ""))),
            6 =>
              New_Conditional
                (Condition => +Exit_Condition,
                 Then_Part => New_Raise (Name => Exit_Ident)),
            7 => (if Update_Stmt = Why_Empty then +Void else Update_Stmt)));

      Loop_Stmt : constant W_Prog_Id :=
        +Insert_Cnt_Loc_Label
           (Ada_Node     => (if Present (Last_Inv) then Last_Inv else Loop_Id),
            E            =>
              New_Loop
                (Ada_Node    => Loop_Id,
                 Code_Before => Loop_Before,
                 Invariants  => User_Invariants,
                 Variants    => Variants,
                 Code_After  => Loop_After),
            Is_Loop_Head => True);

      Try_Body : constant W_Prog_Id :=
        Bind_From_Mapping_In_Prog
          (Params => Params,
           Map    => Map_For_Loop_Entry (Loop_Id),
           Expr   =>
             Sequence
               ((1 =>
                   New_Comment
                     (Comment =>
                        NID
                          ("While loop translating the Ada loop"
                           & (if Sloc (Loop_Id) > 0
                              then
                                " from "
                                & Build_Location_String (Sloc (Loop_Id))
                              else ""))),
                 2 => Loop_Stmt)));

      Loop_Try       : W_Prog_Id;
      Warn_Dead_Code : W_Prog_Id := +Void;

   begin
      --  Now wrap the resulting program in the try-catch block for the
      --  loop, catching the exception corresponding to exiting the loop.

      Loop_Try :=
        New_Try_Block
          (Prog    => Try_Body,
           Handler => (1 => New_Handler (Name => Exit_Ident, Def => +Void)));

      --  Possibly warn on dead code, both when entering the loop and after the
      --  loop. Do not try to check whether the loop condition is statically
      --  disabled if any, it should not happen in practice.

      Loop_Try :=
        Warn_On_Dead_Code
          (First_Stmt, Loop_Try, Params.Phase, Params.Warn_On_Dead);

      if Present (Next_Stmt) then
         Warn_Dead_Code :=
           Warn_On_Dead_Code
             (Next_Stmt, +Void, Params.Phase, Params.Warn_On_Dead);
      end if;

      return
        Sequence
          ((1 =>
              New_Comment
                (Comment =>
                   NID
                     ("Translation of an Ada loop"
                      & (if Sloc (Loop_Id) > 0
                         then " from " & Build_Location_String (Sloc (Loop_Id))
                         else ""))),
            2 =>
              New_Conditional
                (Condition => +Enter_Condition, Then_Part => +Loop_Try),
            3 => Warn_Dead_Code));
   end Wrap_Loop;

end Gnat2Why.Expr.Loops;
