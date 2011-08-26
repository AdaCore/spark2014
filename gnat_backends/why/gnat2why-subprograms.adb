------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Alfa;               use Alfa;
with Atree;              use Atree;
with Debug;
with Einfo;              use Einfo;
with Namet;              use Namet;
with Nlists;             use Nlists;
with Sem_Util;           use Sem_Util;
with Sinfo;              use Sinfo;
with Snames;             use Snames;
with Stand;              use Stand;
with Uintp;              use Uintp;
with VC_Kinds;           use VC_Kinds;

with Alfa.Common;           use Alfa.Common;
with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;

with Why;                   use Why;
with Why.Sinfo;             use Why.Sinfo;
with Why.Atree.Accessors;   use Why.Atree.Accessors;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Mutators;    use Why.Atree.Mutators;
with Why.Atree.Tables;      use Why.Atree.Tables;
with Why.Gen.Arrays;        use Why.Gen.Arrays;
with Why.Gen.Binders;       use Why.Gen.Binders;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Preds;         use Why.Gen.Preds;
with Why.Gen.Progs;         use Why.Gen.Progs;
with Why.Gen.Terms;         use Why.Gen.Terms;
with Why.Types;
with Why.Conversions;       use Why.Conversions;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Driver;       use Gnat2Why.Driver;
with Gnat2Why.Types;        use Gnat2Why.Types;

package body Gnat2Why.Subprograms is

   Result_String : constant String := "___result";
   --  The internal name for the result of an expression

   function Assignment_of_Obj_Decl (N : Node_Id) return W_Prog_Id;
   --  Generate an assignment from an object declaration

   function Case_Expr_Of_Ada_Node (N : Node_Id) return W_Prog_Id;
   --  Build Case expression of Ada Node.

   generic
      with procedure Handle_Argument (Formal, Actual : Node_Id);
   procedure Iterate_Call_Arguments (Call : Node_Id);
   --  Call "Handle_Argument" for each pair Formal/Actual of a function or
   --  procedure call. The node in argument must have a "Name" field and a
   --  "Parameter_Associations" field.

   function Compute_Call_Args (Call : Node_Id) return W_Expr_Array;
   --  Compute arguments for a function call or procedure call. The node in
   --  argument must have a "Name" field and a "Parameter_Associations" field.

   function Compute_Term_Args (Call : Node_Id) return W_Expr_Array;
   --  Same as Compute_Call_Args, but construct terms.

   procedure Compute_Invariant
      (Loop_Body  : List_Id;
       Pred       : out W_Predicate_Id;
       Split_Node : out Node_Id);
   --  Given a list of statements (a loop body), construct a predicate that
   --  corresponds to the conjunction of all assertions at the beginning of
   --  the list. The out parameter Split_Node is set to the last node that is
   --  an assertion.
   --  If there are no assertions, we set Split_Node to N_Empty and we return
   --  True.

   function Int_Expr_Of_Ada_Expr (Expr : Node_Id) return W_Prog_Id;
   --  Translate the given Ada expression to a Why expression of type "int".
   --  More precisely, call Why_Expr_Of_Ada_Expr with argument "Expected_Type"
   --  set to (Kind => Why_Int).

   function Bool_Term_Of_Ada_Expr (Expr : Node_Id) return W_Term_Id;
   --  Translate the given Ada expression to a Why term of type "bool".
   --  More precisely, call Why_Term_Of_Ada_Expr with argument "Expected_Type"
   --  set to New_Type_Bool.

   function Effect_Is_Empty (E : W_Effects_Id) return Boolean;
   --  Test if the effect in argument is empty.

   procedure Extract_From_Quantified_Expression
      (N          : Node_Id;
       Index      : out W_Identifier_Id;
       Range_Expr : out Node_Id);
   --  Extract the loop index and the range expression node from a
   --  QUANTIFIED_EXPRESSION

   function Int_Term_Of_Ada_Expr (Expr : Node_Id) return W_Term_Id;
   --  Translate the given Ada expression to a Why term of type "int".
   --  More precisely, call Why_Term_Of_Ada_Expr with argument "Expected_Type"
   --  set to (Kind => Why_Int).

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id;
   --  Return the Defining_Identifier of the loop that belongs to an exit
   --  statement.

   function Predicate_Of_Pragma_Check (N : Node_Id) return W_Predicate_Id;
   --  Compute a Why predicate from a node of kind Pragma Check. Raise
   --  Not_Implemented if it is not a Pragma Check.

   function Prog_Equal_To (E : W_Prog_Id; N : Node_Id) return W_Prog_Id;
   --  For an expression E of type "int" and a Node that represents a
   --  Discrete_Choice, build an expression that expresses that T belongs to
   --  the range expressed by N.

   function Range_Predicate (N : Node_Id; T : W_Term_Id)
      return W_Predicate_Id;
   --  Generate a predicate of the form
   --    low_bound < int_of_type (x) < high_bound
   --  from an N_Range node.

   function Range_Prog (N : Node_Id; T : W_Prog_Id)
      return W_Prog_Id;
   --  Same as Range_Predicate, but for programs.

   function Term_Equal_To (T : W_Term_Id; N : Node_Id) return W_Term_Id;
   --  For a term T of type "int" and a Node that represents a
   --  Discrete_Choice, build a term that expresses that T belongs to the
   --  range expressed by N.

   function Unit_Param return Binder_Type;
   --  return a dummy binder for a single argument of type unit
   --
   function Why_Expr_Of_Ada_Enum
     (Enum         : Node_Id;
      Current_Type : out Why_Type;
      Domain       : EW_Domain)
      return W_Expr_Id;
   --  Translate an Ada enumeration literal to Why. There are a number of
   --  special cases, so its own function is appropriate.

   function Why_Expr_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Why_Type) return W_Prog_Id;
   --  Translate a single Ada expression into a Why expression of the
   --  Expected_Type.
   --  When VC_Mode is true, allow a translation to Why code that will only
   --  trigger safety VCs, but is not equivalent.

   function Why_Expr_Of_Ada_Expr (Expr : Node_Id) return W_Prog_Id;
   --  Same as the previous function, but use the type of Expr as the expected
   --  type.

   function Why_Expr_Of_Ada_Stmts
     (Stmts      : List_Id;
      Start_From : Node_Id := Empty)
     return W_Prog_Id;
   --  Translate a list of Ada statements into a single Why expression.
   --  An empty list is translated to "void".
   --  The parameter Start_From indicates a node in the list from which the
   --  translation process is to be started. All nodes before and including
   --  Start_From are ignored.

   function Why_Ident_Of_Ada_Ident (Id : Node_Id) return W_Identifier_Id;
   --  Build a Why identifier out of an Ada Node.

   function Why_Binop_Of_Ada_Op (Op : N_Binary_Op) return EW_Binary_Op;
   --  Convert an Ada binary operator to a Why term symbol

   function Why_Rel_Of_Ada_Op (Op : N_Op_Compare) return EW_Relation;
   --  Convert an Ada comparison operator to a Why relation symbol

   function Wrap_Loop
      (Loop_Body : W_Prog_Id;
       Condition : W_Prog_Id;
       Loop_Name : String;
       Invariant : W_Predicate_Id;
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

   function Assignment_of_Obj_Decl (N : Node_Id) return W_Prog_Id
   is
      Lvalue   : constant Entity_Id := Defining_Identifier (N);
      Rexpr    : constant Node_Id := Expression (N);
   begin

      --  In our Why translation, all objects are declared at top-level.
      --  Object declarations in Ada inside Subprograms are therefore
      --  translated to assignments to initialize these objects.
      --  We can only generate an assignment when the Lvalue is mutable; if it
      --  is not, there are two cases. If the expression is static, we already
      --  have generated an axiom upon declaration of the object, and we are
      --  done. If it is not, we replace the assignment by an assumption of
      --  the following form:

      --  let var_name__assume = <rexpr> in
      --    assume (var_name = var_name_assume);

      if Present (Rexpr) then
         declare
            Why_Expr : constant W_Prog_Id :=
                         Why_Expr_Of_Ada_Expr (Rexpr, Type_Of_Node (Lvalue));
            L_Name   : constant String := Full_Name (Lvalue);
            L_Id     : constant W_Identifier_Id := New_Identifier (L_Name);
         begin
            if Is_Mutable (Lvalue) then
               return New_Assignment
                 (Ada_Node => N,
                  Domain   => EW_Prog,
                  Name     => L_Id,
                  Value    => Why_Expr);

            elsif Is_Static_Expression (Rexpr) then

               --  We generate an ignore statement, to obtain all the checks
               --  ??? Is this necessary? after all, we would get a compiler
               --  warning anyway

               return New_Ignore (Prog => Why_Expr);

            else
               declare
                  Tmp_Var : constant W_Identifier_Id :=
                              Assume_Name.Id (L_Name);
                  Eq      : constant W_Predicate_Id :=
                              New_Equal (+Tmp_Var, +L_Id);
               begin
                  return
                    New_Binding
                      (Domain   => EW_Prog,
                       Ada_Node => N,
                       Name     => Tmp_Var,
                       Def      => Why_Expr,
                       Context  =>
                         +New_Assume_Statement
                           (Ada_Node => N,
                            Pred     => Eq));
               end;
            end if;
         end;
      else
         return New_Void (N);
      end if;
   end Assignment_of_Obj_Decl;

   ---------------------------
   -- Case_Expr_Of_Ada_Node --
   ---------------------------

   function Case_Expr_Of_Ada_Node (N : Node_Id) return W_Prog_Id
   is
      --  For a given case expression
      --
      --    case X is
      --       when Case_1 => S1
      --       ...
      --       when Case_n => Sn
      --       when others => S
      --    end case;
      --
      --  We generate nested if expressions:
      --    if X = Case_1 then S1
      --    else if ...
      --    else if X = Case_N then Sn
      --    else S

      -----------------
      -- Branch_Expr --
      -----------------

      function Branch_Expr (N : Node_Id) return W_Prog_Id;
      --  Return the expression that corresponds to a branch; decide which
      --  function to call depending on the type of the branch.

      function Branch_Expr (N : Node_Id) return W_Prog_Id
      is
      begin
         case Nkind (N) is
            when N_Case_Expression_Alternative =>
               return Why_Expr_Of_Ada_Expr (Expression (N));

            when N_Case_Statement_Alternative =>
               return Why_Expr_Of_Ada_Stmts (Statements (N));

            when others =>
               raise Unexpected_Node;

         end  case;
      end Branch_Expr;

      Cur_Case     : Node_Id := Last (Alternatives (N));
      Matched_Expr : constant W_Prog_Id :=
                       Int_Expr_Of_Ada_Expr (Expression (N));

      --  We always take the last branch as the default value
      T            : W_Prog_Id := Branch_Expr (Cur_Case);

      --  beginning of processing for Case_Expr_Of_Ada_Node
   begin
      Cur_Case := Prev (Cur_Case);
      while Present (Cur_Case) loop
         declare
            Cur_Choice : Node_Id := First (Discrete_Choices (Cur_Case));
            C          : W_Prog_Id :=
                           New_Literal
                             (Domain => EW_Prog,
                              Value  => EW_False);
         begin
            while Present (Cur_Choice) loop
               C := New_Prog_Orb_Else
                      (C,
                       Prog_Equal_To (Matched_Expr, Cur_Choice));
               Next (Cur_Choice);
            end loop;

            declare
               Then_Part : W_Prog_Id;
            begin
               case Nkind (Cur_Case) is
                  when N_Case_Expression_Alternative =>
                     Then_Part :=
                        Why_Expr_Of_Ada_Expr (Expression (Cur_Case));

                  when N_Case_Statement_Alternative =>
                     Then_Part :=
                        Why_Expr_Of_Ada_Stmts (Statements (Cur_Case));

                  when others =>
                     raise Unexpected_Node;

               end  case;
               T :=
                  New_Simpl_Conditional_Prog
                     (Condition => C,
                      Then_Part => Then_Part,
                      Else_Part => T);
            end;
         end;
         Prev (Cur_Case);
      end loop;
      return T;
   end Case_Expr_Of_Ada_Node;

   ----------------------------
   -- Iterate_Call_Arguments --
   ----------------------------

   procedure Iterate_Call_Arguments (Call : Node_Id)
   is
      Params     : constant List_Id := Parameter_Associations (Call);
      Cur_Formal : Node_Id := First_Entity (Entity (Name (Call)));
      Cur_Actual : Node_Id := First (Params);
      In_Named   : Boolean := False;
   begin
      --  We have to deal with named arguments, but the frontend has
      --  done some work for us. All unnamed arguments come first and
      --  are given as-is, while named arguments are wrapped into a
      --  N_Parameter_Association. The field First_Named_Actual of the
      --  function or procedure call points to the first named argument,
      --  that should be inserted after the last unnamed one. Each
      --  Named Actual then points to a Next_Named_Actual. These
      --  pointers point directly to the actual, but Next_Named_Actual
      --  pointers are attached to the N_Parameter_Association, so to
      --  get the next actual from the current one, we need to follow
      --  the Parent pointer.
      --
      --  The Boolean In_Named states how to obtain the next actual:
      --  either follow the Next pointer, or the Next_Named_Actual of
      --  the parent.
      --  We start by updating the Cur_Actual and In_Named variables for
      --  the first parameter.

      if Nkind (Cur_Actual) = N_Parameter_Association then
         In_Named := True;
         Cur_Actual := First_Named_Actual (Call);
      end if;

      while Present (Cur_Formal) and then Present (Cur_Actual) loop
         Handle_Argument (Cur_Formal, Cur_Actual);
         Cur_Formal := Next_Entity (Cur_Formal);

         if In_Named then
            Cur_Actual := Next_Named_Actual (Parent (Cur_Actual));
         else
            Next (Cur_Actual);

            if Nkind (Cur_Actual) = N_Parameter_Association then
               In_Named := True;
               Cur_Actual := First_Named_Actual (Call);
            end if;
         end if;
      end loop;
   end Iterate_Call_Arguments;

   -----------------------
   -- Compute_Call_Args --
   -----------------------

   function Compute_Call_Args (Call : Node_Id) return W_Expr_Array
   is
      Params : constant List_Id := Parameter_Associations (Call);
      Len    : constant Nat := List_Length (Params);
   begin
      if Len = 0 then
         return (1 => New_Void (Call));
      end if;

      declare
         Why_Args : W_Expr_Array := (1 .. Integer (Len) => <>);
         Cnt      : Positive := 1;

         procedure Compute_Arg (Formal, Actual : Node_Id);
         --  Compute a Why expression for each parameter

         -----------------
         -- Compute_Arg --
         -----------------

         procedure Compute_Arg (Formal, Actual : Node_Id)
         is
         begin
            case Ekind (Formal) is
               when E_In_Out_Parameter | E_Out_Parameter =>
                  --  Parameters that are "out" must be variables
                  --  They are translated "as is"
                  Why_Args (Cnt) := +Why_Ident_Of_Ada_Ident (Actual);

               when others =>
                  --  No special treatment for parameters that are
                  --  not "out"
                  Why_Args (Cnt) :=
                    +Why_Expr_Of_Ada_Expr (Actual, Type_Of_Node (Formal));
            end case;
            Cnt := Cnt + 1;
         end Compute_Arg;

         procedure Iterate_Prog_Call is new
           Iterate_Call_Arguments (Compute_Arg);
      begin
         Iterate_Prog_Call (Call);
         return Why_Args;
      end;
   end Compute_Call_Args;

   -----------------------
   -- Compute_Term_Args --
   -----------------------

   function Compute_Term_Args (Call : Node_Id) return W_Expr_Array
   is
      Params : constant List_Id := Parameter_Associations (Call);
      Len    : constant Nat := List_Length (Params);
   begin
      if Len = 0 then
         return (1 => New_Void);
      end if;

      declare
         Why_Args : W_Expr_Array := (1 .. Integer (Len) => <>);
         Cnt      : Positive := 1;

         procedure Compute_Arg (Formal, Actual : Node_Id);
         --  Compute a Why term for each parameter

         -----------------
         -- Compute_Arg --
         -----------------

         procedure Compute_Arg (Formal, Actual : Node_Id) is
         begin
            Why_Args (Cnt) :=
               +Why_Term_Of_Ada_Expr
                  (Actual, Type_Of_Node (Formal));
            Cnt := Cnt + 1;
         end Compute_Arg;

         procedure Iterate_Term_Call is new
            Iterate_Call_Arguments (Compute_Arg);
      begin
         Iterate_Term_Call (Call);
         return Why_Args;
      end;
   end Compute_Term_Args;

   -----------------------
   -- Compute_Invariant --
   -----------------------

   procedure Compute_Invariant
      (Loop_Body  : List_Id;
       Pred       : out W_Predicate_Id;
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
                 New_Simpl_Conjunction
                   (Left => Pred,
                    Right => Predicate_Of_Pragma_Check (Cur_Stmt));

            when others =>
               exit;
         end case;

         Split_Node := Cur_Stmt;
         Nlists.Next (Cur_Stmt);
      end loop;
   end Compute_Invariant;

   function Effect_Is_Empty (E : W_Effects_Id) return Boolean is
   begin
      return
        (Is_Empty (+Effects_Get_Reads (E)) and then
         Is_Empty (+Effects_Get_Writes (E)));
   end Effect_Is_Empty;

   procedure Extract_From_Quantified_Expression
      (N          : Node_Id;
       Index      : out W_Identifier_Id;
       Range_Expr : out Node_Id)
   is
      Spec : Node_Id;
   begin
      if Present (Loop_Parameter_Specification (N)) then
         Spec := Loop_Parameter_Specification (N);
         Range_Expr := Discrete_Subtype_Definition (Spec);

      elsif Present (Iterator_Specification (N)) then
         Spec := Iterator_Specification (N);
         Range_Expr := Name (Spec);

      else
         --  None of Loop_Parameter_Specification and
         --  Iterator_Specification is present in the node; abort
         raise Program_Error;
      end if;

      Index := New_Identifier (Full_Name (Defining_Identifier (Spec)));
   end Extract_From_Quantified_Expression;

   ---------------
   -- Get_Range --
   ---------------

   function Get_Range (N : Node_Id) return Node_Id is
   begin
      case Nkind (N) is
         when N_Range
           | N_Real_Range_Specification
           | N_Signed_Integer_Type_Definition
           | N_Floating_Point_Definition =>
            return N;

         when N_Subtype_Indication =>
            return Range_Expression (Constraint (N));

         when N_Identifier | N_Expanded_Name =>
            return Get_Range (Entity (N));

         when N_Defining_Identifier =>
            case Ekind (N) is
               when Discrete_Kind =>
                  return Scalar_Range (N);

               when Object_Kind =>
                  return Scalar_Range (Etype (N));

               when others =>
                  raise Program_Error;

            end case;

         when others =>
            raise Program_Error;
      end case;
   end Get_Range;

   ---------------------
   -- Range_Predicate --
   ---------------------

   function Range_Predicate (N : Node_Id; T : W_Term_Id) return W_Predicate_Id
   is
   begin
      return
        New_Relation
          (Domain => EW_Term,
           Left   => +Int_Term_Of_Ada_Expr (Low_Bound (N)),
           Op     => EW_Le,
           Right  => +T,
           Op2    => EW_Le,
           Right2 => +Int_Term_Of_Ada_Expr (High_Bound (N)));
   end Range_Predicate;

   ----------------
   -- Range_Prog --
   ----------------

   function Range_Prog (N : Node_Id; T : W_Prog_Id) return W_Prog_Id is
   begin
      return
        New_Prog_Andb_Then
          (Left =>
             New_Relation
               (Domain => EW_Prog,
                Op     => EW_Le,
                Left   => +Int_Expr_Of_Ada_Expr (Low_Bound (N)),
                Right  => +T),
           Right =>
             New_Relation
               (Domain => EW_Prog,
                Op     => EW_Le,
                Left   => +T,
                Right  => +Int_Expr_Of_Ada_Expr (High_Bound (N))));
   end Range_Prog;

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

   -------------------------------
   -- Predicate_Of_Pragma_Check --
   -------------------------------

   function Predicate_Of_Pragma_Check (N : Node_Id) return W_Predicate_Id is
   begin
      if Get_Pragma_Id (Pragma_Name (N)) = Pragma_Check then
         declare
            Arg1 : Node_Id;
            Arg2 : Node_Id;
         begin
            if Present (Pragma_Argument_Associations (N)) then
               Arg1 := First (Pragma_Argument_Associations (N));

               if Present (Arg1) then
                  Arg2 := Next (Arg1);
               end if;
            end if;

            if Present (Expression (Arg2)) then
               return Why_Predicate_Of_Ada_Expr (Expression (Arg2));

            else
               raise Program_Error;
            end if;
         end;

      else
         raise Not_Implemented;
      end if;
   end Predicate_Of_Pragma_Check;

   -------------------
   -- Prog_Equal_To --
   -------------------

   function Prog_Equal_To (E : W_Prog_Id; N : Node_Id) return W_Prog_Id
   is
   begin
      case Nkind (N) is
         when N_Identifier
           | N_Real_Literal
           | N_Integer_Literal =>
            return
              New_Prog_Boolean_Cmp
                (Cmp   => EW_Eq,
                 Left  => E,
                 Right => Why_Expr_Of_Ada_Expr ((N), Base_Why_Type (N)));

         when N_Range =>
            return
              New_Prog_Andb
                (Left  =>
                   New_Prog_Boolean_Cmp
                     (Cmp   => EW_Le,
                      Left  => Int_Expr_Of_Ada_Expr (Low_Bound (N)),
                      Right => E),
                 Right =>
                   New_Prog_Boolean_Cmp
                     (Cmp   => EW_Le,
                      Left  => E,
                      Right =>
                        Int_Expr_Of_Ada_Expr (Low_Bound (N))));

         when N_Others_Choice =>
            return New_Literal (Value => EW_True);

         when others =>
            raise Not_Implemented;

      end case;
   end Prog_Equal_To;

   -------------------
   -- Term_Equal_To --
   -------------------

   function Term_Equal_To (T : W_Term_Id; N : Node_Id) return W_Term_Id
   is
   begin
      case Nkind (N) is
         when N_Identifier
           | N_Integer_Literal
           | N_Real_Literal =>
            return
              New_Boolean_Cmp
                (Cmp   => EW_Eq,
                 Left  => T,
                 Right => Why_Term_Of_Ada_Expr (N, Base_Why_Type (N)));

         when N_Range =>
            return
              New_Andb
                (Left  =>
                   New_Boolean_Cmp
                     (Cmp   => EW_Le,
                      Left  => Int_Term_Of_Ada_Expr (Low_Bound (N)),
                      Right => T),
                 Right =>
                   New_Boolean_Cmp
                     (Cmp   => EW_Le,
                      Left  => T,
                      Right => Int_Term_Of_Ada_Expr (Low_Bound (N))));

         when N_Others_Choice =>
            return New_Literal (Value => EW_True);

         when others =>
            raise Not_Implemented;

      end case;
   end Term_Equal_To;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return Entity_Id is
   begin
      if Nkind (N) in N_Entity
        and then Ekind (N) in Type_Kind
      then
         return N;
      else
         return Etype (N);
      end if;
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return String
   is
      E : constant Entity_Id := Type_Of_Node (N);
   begin
      if E = Standard_Boolean then
         return Why_Scalar_Type_Name (Why_Bool);
      else
         return Full_Name (E);
      end if;
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return Why_Type
   is
      E : constant Entity_Id := Type_Of_Node (N);
   begin
      if E = Standard_Boolean then
         return Why_Bool_Type;
      else
         return Why_Abstract (E);
      end if;
   end Type_Of_Node;

   ----------------
   -- Unit_Param --
   ----------------

   function Unit_Param return Binder_Type is
   begin
      return
        (B_Name   => New_Identifier ("__void_param"),
         B_Type   => New_Base_Type (Base_Type => EW_Unit),
         Modifier => None,
         Ada_Node => Empty);
   end Unit_Param;

   --------------------------------
   -- Why_Decl_Of_Ada_Subprogram --
   --------------------------------

   procedure Why_Decl_Of_Ada_Subprogram
     (File    : W_File_Id;
      Node    : Node_Id;
      As_Spec : Boolean)
   is
      Spec        : constant Node_Id :=
                      (if Nkind (Node) = N_Subprogram_Body and then
                         Present (Corresponding_Spec (Node))
                       then
                         (if Nkind (Parent (Corresponding_Spec (Node))) =
                            N_Defining_Program_Unit_Name
                          then
                            Parent (Parent (Corresponding_Spec (Node)))
                          else
                            Parent (Corresponding_Spec (Node)))
                       else
                         Specification (Node));
      Name_Str    : constant String  :=
                      Get_Name_String (Chars (Defining_Entity (Spec)));
      Ada_Binders : constant List_Id := Parameter_Specifications (Spec);
      Arg_Length  : constant Nat := List_Length (Ada_Binders);

      function Compute_Binders return Binder_Array;
      --  Compute the arguments of the generated Why function;
      --  use argument (x : void) if the Ada procedure / function has no
      --  arguments.

      function Compute_Context (Initial_Body : W_Prog_Id) return W_Prog_Id;
      --  Deal with object declarations at the beginning of the function.
      --  For local variables that originate from the source, simply assign
      --  the new value to the variable; Such variables have been declared
      --  globally.
      --  For local variables that are introduced by the compiler, add a "let"
      --  binding to Why body for each local variable of the procedure.

      function Compute_Effects return W_Effects_Id;
      --  Compute the effects of the generated Why function.

      generic
         type T is private;
         Basic_Value : T;
         with function Mapping (N : Node_Id) return T;
         with function Combine (Left, Right : T) return T;
      function Compute_Spec
         (Kind       : Name_Id;
          Located_Node : out Node_Id) return T;
      --  Compute the precondition of the generated Why functions.
      --  Pass the Kind Name_Precondition or Name_Postcondition to decide if
      --  you want the pre- or postcondition.
      --  Also output a suitable location node, if available.

      function Is_Syntactic_Expr_Function return Node_Id;
      --  Compute if Node is an expression function in the source, also works
      --  for the declaration of an expression function.
      --  If Is_Syntactic_Expr_Function'Result is equal to Node, Node is not
      --  an expression function; otherwise, Is_Syntactic_Expr_Function'Result
      --  is the original node of the expression function.

      ---------------------
      -- Compute_Binders --
      ---------------------

      function Compute_Binders return Binder_Array
      is
         Cur_Binder : Node_Id := First (Ada_Binders);
         Cnt        : Integer := 1;
         Result     : Binder_Array :=
                        (1 .. Integer (Arg_Length) => <>);
      begin
         while Present (Cur_Binder) loop
            declare
               Id   : constant Node_Id :=
                        Defining_Identifier (Cur_Binder);
               Name : constant W_Identifier_Id :=
                        Why_Ident_Of_Ada_Ident (Id);
            begin
               Result (Cnt) :=
                 (Ada_Node => Cur_Binder,
                  B_Name   => Name,
                  Modifier =>
                    (if Is_Mutable (Id) then Ref_Modifier else None),
                  B_Type => +Why_Prog_Type_Of_Ada_Obj (Id, True));
               Next (Cur_Binder);
               Cnt := Cnt + 1;
            end;
         end loop;
         return Result;
      end Compute_Binders;

      ---------------------
      -- Compute_Context --
      ---------------------

      function Compute_Context (Initial_Body : W_Prog_Id) return W_Prog_Id
      is
         Cur_Decl : Node_Id := Last (Declarations (Node));
         R        : W_Prog_Id := Initial_Body;
      begin
         while Nkind (Cur_Decl) /= N_Empty loop
            case Nkind (Cur_Decl) is
               when N_Object_Declaration =>
                  R := Sequence (Assignment_of_Obj_Decl (Cur_Decl), R);

               when others =>
                  null;

            end case;
            Cur_Decl := Prev (Cur_Decl);
         end loop;

         --  Enclose the subprogram body in a try-block, so that return
         --  statements can be translated as raising exceptions.

         declare
            Raise_Stmt : constant W_Prog_Id :=
                           New_Raise
                             (Ada_Node => Node,
                              Name     => New_Result_Exc_Identifier.Id);
            Result_Var : constant W_Prog_Id :=
                           (if Nkind (Spec) = N_Function_Specification then
                              New_Unary_Op
                                (Domain   => EW_Prog,
                                 Ada_Node => Node,
                                 Op       => EW_Deref,
                                 Right    => +New_Result_Temp_Identifier.Id)
                            else New_Void);
         begin
            R :=
              New_Try_Block
                (Prog    => Sequence (R, Raise_Stmt),
                 Handler =>
                   (1 =>
                      New_Handler
                        (Name => New_Result_Exc_Identifier.Id,
                         Def  => Result_Var)));
         end;

         --  Declare a local variable to hold the result of a function

         if Nkind (Spec) = N_Function_Specification then
            declare
               Rvalue : constant W_Prog_Id :=
                          New_Simpl_Any_Expr
                            (New_Abstract_Type
                               (Name =>
                                  New_Identifier (Type_Of_Node
                                    (Defining_Entity (Spec)))));
            begin
               R :=
                 New_Binding_Ref
                   (Ada_Node => Cur_Decl,
                    Name     => New_Result_Temp_Identifier.Id,
                    Def      => Rvalue,
                    Context  => R);
            end;
         end if;

         return R;
      end Compute_Context;

      ---------------------
      -- Compute_Effects --
      ---------------------

      function Compute_Effects return W_Effects_Id is
         E               : constant Entity_Id := Unique_Defining_Entity (Node);
         Read_Names      : Name_Set.Set;
         Write_Names     : Name_Set.Set;
         Write_All_Names : UString_Set.Set;
         Eff             : constant W_Effects_Id := New_Effects;

      begin
         --  Collect global variables potentially read and written

         Read_Names  := Get_Reads (E);
         Write_Names := Get_Writes (E);

         --  Workaround for K526-008 and K525-019

         --  for Name of Write_Names loop
         --     Write_All_Names.Include (To_Unbounded_String (Name.all));
         --  end loop;

         declare
            use Name_Set;

            C : Cursor := Write_Names.First;
         begin
            while C /= No_Element loop
               Write_All_Names.Include (To_Unbounded_String (Element (C).all));
               Next (C);
            end loop;
         end;

         --  Add all OUT and IN OUT parameters as potential writes

         declare
            Arg : Node_Id;
            Id  : Entity_Id;
         begin
            if Is_Non_Empty_List (Ada_Binders) then
               Arg := First (Ada_Binders);
               while Present (Arg) loop
                  Id := Defining_Identifier (Arg);

                  if Ekind_In (Id, E_Out_Parameter, E_In_Out_Parameter) then
                     Write_All_Names.Include
                       (To_Unbounded_String (Full_Name (Id)));
                  end if;

                  Next (Arg);
               end loop;
            end if;
         end;

         --  Workaround for K526-008 and K525-019

         --  for Name of Read_Names loop
         --     Effects_Append_To_Reads (Eff, New_Identifier (Name.all));
         --  end loop;

         declare
            use Name_Set;

            C : Cursor := Read_Names.First;
         begin
            while C /= No_Element loop
               Effects_Append_To_Reads (Eff, New_Identifier (Element (C).all));
               Next (C);
            end loop;
         end;

         --  Workaround for K526-008 and K525-019

         --  for Name of Write_All_Names loop
         --     Effects_Append_To_Writes (Eff,
         --                               New_Identifier (To_String (Name)));
         --  end loop;

         declare
            use UString_Set;

            C : Cursor := Write_All_Names.First;
         begin
            while C /= No_Element loop
               Effects_Append_To_Writes (Eff,
                                         New_Identifier
                                           (To_String (Element (C))));
               Next (C);
            end loop;
         end;

         return +Eff;
      end Compute_Effects;

      ------------------
      -- Compute_Spec --
      ------------------

      function Compute_Spec
         (Kind       : Name_Id;
          Located_Node : out Node_Id) return T
      is
         Corr_Spec      : Node_Id;
         Cur_Spec       : T := Basic_Value;
         Found_Location : Boolean := False;
         PPCs           : Node_Id;

      begin
         if Nkind (Node) = N_Subprogram_Declaration then
            Corr_Spec := Defining_Entity (Spec);
         else
            Corr_Spec := Corresponding_Spec (Node);
         end if;

         if Nkind (Corr_Spec) = N_Empty then
            return Cur_Spec;
         end if;

         PPCs := Spec_PPC_List (Contract (Corr_Spec));
         while Present (PPCs) loop
            if Pragma_Name (PPCs) = Kind then
               declare
                  Ada_Spec : constant Node_Id :=
                               Expression
                                 (First (Pragma_Argument_Associations (PPCs)));
               begin
                  if not Found_Location then
                     Located_Node := Ada_Spec;
                     Found_Location := True;
                  end if;

                  Cur_Spec :=
                     Combine
                       (Left  => Mapping (Ada_Spec),
                        Right => Cur_Spec);
               end;
            end if;

            PPCs := Next_Pragma (PPCs);
         end loop;

         return Cur_Spec;
      end Compute_Spec;

      function Compute_Spec_Pred is new
        Compute_Spec
          (W_Predicate_Id,
           New_Literal (Value => EW_True),
           Why_Predicate_Of_Ada_Expr,
           New_Simpl_Conjunction);

      function Compute_Spec_Prog is new
        Compute_Spec
          (W_Prog_Id,
           New_Literal (Value => EW_True),
           Why_Expr_Of_Ada_Expr,
           New_Prog_Andb_Then);

      --------------------------------
      -- Is_Syntactic_Expr_Function --
      --------------------------------

      function Is_Syntactic_Expr_Function return Node_Id
      is
         Tmp_Node : Node_Id := Original_Node (Parent (Spec));
      begin
         --  Usually, it is sufficient to check for the original node of the
         --  function (but for some reason we have to descend to the spec and
         --  move up to another parent).

         if Nkind (Tmp_Node) = N_Expression_Function then
            return Tmp_Node;
         end if;

         --  But if we are at the function declaration, it is possible that
         --  the function definition is given later, using an expression
         --  function. We check this second possibility here.

         if Nkind (Node) = N_Subprogram_Declaration then
            Tmp_Node :=
              Original_Node (Parent (Parent (Corresponding_Body (Node))));

            if Nkind (Tmp_Node) = N_Expression_Function then
               return Tmp_Node;
            end if;

         --  ??? I don't know in which situation we need this case ...

         else
            Tmp_Node :=
               Original_Node (Parent (Parent (Corresponding_Spec (Node))));

            if Nkind (Tmp_Node) = N_Expression_Function then
               return Tmp_Node;
            end if;
         end if;

         return Node;
      end Is_Syntactic_Expr_Function;

      Func_Binders : constant Binder_Array := Compute_Binders;
      Ext_Binders  : constant Binder_Array :=
         (if Arg_Length = 0 then (1 => Unit_Param)
          else Func_Binders);
      Dummy_Node : Node_Id;
      Pre          : constant W_Predicate_Id :=
         Compute_Spec_Pred (Name_Precondition, Dummy_Node);
      Loc_Node     : Node_Id := Empty;
      Post         : constant W_Predicate_Id :=
         Compute_Spec_Pred (Name_Postcondition, Loc_Node);
      Orig_Node : constant Node_Id := Is_Syntactic_Expr_Function;
      Effects      : constant W_Effects_Id := Compute_Effects;
      Is_Expr_Func : constant Boolean :=
                       Nkind (Spec) = N_Function_Specification
                         and then
                       Effect_Is_Empty (Effects)
                         and then
                       Orig_Node /= Node
                         and then
                       Get_Kind (+Post) = W_Literal
                         and then
                       Literal_Get_Value (W_Literal_Id (Post)) = EW_True;

   --  Start of processing for Why_Decl_Of_Ada_Subprogram

   begin
      if Nkind (Node) = N_Subprogram_Body
        and then not As_Spec
      then
         Emit
           (File,
            New_Function_Def
              (Domain  => EW_Prog,
               Name    => New_Pre_Check_Name.Id (Name_Str),
               Binders => Ext_Binders,
               Def     =>
                 +Compute_Spec_Prog (Name_Precondition, Dummy_Node)));

         if Is_Expr_Func then
            if Etype (Defining_Entity (Spec)) = Standard_Boolean then
               Emit
                 (File,
                  New_Defining_Bool_Axiom
                    (Name    => Logic_Func_Name.Id (Name_Str),
                     Binders => Ext_Binders,
                     Pre     => Pre,
                     Def     => Why_Predicate_Of_Ada_Expr
                                  (Expression (Orig_Node))));

            else
               Emit
                 (File,
                  New_Defining_Axiom
                    (Name    => Logic_Func_Name.Id (Name_Str),
                     Binders => Ext_Binders,
                     Pre     => Pre,
                     Def     => Why_Term_Of_Ada_Expr
                                  (Expression (Orig_Node))));
            end if;
         end if;

         if not Debug.Debug_Flag_Dot_GG then
            Emit
              (File,
               New_Function_Def
                 (Domain  => EW_Prog,
                  Name    => New_Definition_Name.Id (Name_Str),
                  Binders => (1 => Unit_Param),
                  Pre     => Pre,
                  Post    =>
                    +New_Located_Expr
                      (Loc_Node,
                       +Post,
                       VC_Postcondition,
                       EW_Pred),
                  Def     =>
                    +Compute_Context
                      (Why_Expr_Of_Ada_Stmts
                        (Statements
                          (Handled_Statement_Sequence (Node))))));
         end if;

      else
         declare
            Ret_Type   : constant W_Primitive_Type_Id :=
                           (if Nkind (Spec) = N_Function_Specification then
                              +Why_Logic_Type_Of_Ada_Type
                                (Entity (Result_Definition (Spec)))
                            else
                              New_Base_Type (Base_Type => EW_Unit));
            Param_Post : constant W_Predicate_Id :=
                           (if Is_Expr_Func then
                              (if Entity (Result_Definition (Spec)) =
                                              Standard_Boolean
                               then
                                 New_Equal_Bool
                                   (Left  => New_Result_Term,
                                    Right =>
                                      Why_Predicate_Of_Ada_Expr
                                        (Expression (Orig_Node)))
                               else
                                 New_Equal
                                   (Left  => New_Result_Term,
                                    Right =>
                                      Why_Term_Of_Ada_Expr
                                        (Expression (Orig_Node))))
                            else Post);
         begin
            Emit
              (File,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Program_Func_Name.Id (Name_Str),
                  Binders     => Ext_Binders,
                  Return_Type => Ret_Type,
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => Param_Post));

            if Is_Expr_Func then
               Emit
                 (File,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => Logic_Func_Name.Id (Name_Str),
                     Binders     => Ext_Binders,
                     Return_Type =>
                       +Why_Logic_Type_Of_Ada_Type
                         (Etype (Defining_Entity (Spec)))));
            end if;
         end;
      end if;
   end Why_Decl_Of_Ada_Subprogram;

   --------------------------
   -- Why_Expr_Of_Ada_Enum --
   --------------------------

   function Why_Expr_Of_Ada_Enum
     (Enum         : Node_Id;
      Current_Type : out Why_Type;
      Domain       : EW_Domain)
      return W_Expr_Id is
   begin
      --  Deal with special cases: True/False for boolean values

      if Entity (Enum) = Standard_True then
         Current_Type := (Kind => Why_Bool);
         return New_Literal (Value => EW_True, Domain => Domain);
      end if;

      if Entity (Enum) = Standard_False then
         Current_Type := (Kind => Why_Bool);
         return New_Literal (Value => EW_False, Domain => Domain);
      end if;

      --  In the case of a subtype of an enumeration, we need to insert a
      --  conversion. We do so here by modifying the Current_Type; the
      --  conversion itself will be inserted by Why_Expr_Of_Ada_Expr.

      case Ekind (Etype (Enum)) is
         when E_Enumeration_Subtype =>
            Current_Type := Why_Abstract (Etype (Entity (Enum)));

         when others =>
            null;
      end case;

      return +Why_Ident_Of_Ada_Ident (Enum);
   end Why_Expr_Of_Ada_Enum;

   --------------------------
   -- Why_Expr_Of_Ada_Expr --
   --------------------------

   function Why_Expr_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Why_Type) return W_Prog_Id
   is
      T            : W_Prog_Id;
      Current_Type : Why_Type := Type_Of_Node (Expr);
      Overflow_Check_Needed : Boolean := False;
   begin
      --  Here, we simply analyze the structure of Expr and build the
      --  corresponding Why expression. When necessary, we update the
      --  variable Current_Type, which is compared at the very end of this
      --  function with the argument Expected_Type. If they are different, a
      --  conversion is inserted.
      --
      --  This function translates all arithmetic operations on Ada integer
      --  types to '+' in Why. This means that conversions must be added. The
      --  Expected_Type is adjusted accordingly for recursive calls.

      --  ??? TBD: complete this function for the remaining cases
      case Nkind (Expr) is
         when N_Integer_Literal =>
            T :=
              New_Integer_Constant
                (Domain   => EW_Prog,
                 Ada_Node => Expr,
                 Value    => Intval (Expr));
            Current_Type := Why_Int_Type;

         when N_Real_Literal =>
            --  The original is usually much easier to process for alt-ergo
            --  than the rewritten node; typically, the will be in decimal
            --  base whereas the expanded node will be of the form
            --  (Num / (2 ** Den)). The division is a problem for alt-ergo,
            --  even between two litterals.

            if Is_Rewrite_Substitution (Expr) then
               begin
                  T := Why_Expr_Of_Ada_Expr (Original_Node (Expr),
                                             Why_Real_Type);

               --  It may happen that the original node is not in
               --  alfa, whereas the rewritten one is: typically,
               --  if the original node uses exponentiation. So try
               --  the original node and fall back to the rewritten
               --  node if failed.

               exception
                  when Not_Implemented =>
                     T :=
                       New_Real_Constant
                         (Domain   => EW_Prog,
                          Ada_Node => Expr,
                          Value    => Realval (Expr));
               end;

            else
               T :=
                 New_Real_Constant
                   (Domain   => EW_Prog,
                    Ada_Node => Expr,
                    Value    => Realval (Expr));
            end if;

            Current_Type := Why_Real_Type;

         --  Deal with identifiers:
         --  * Enumeration literals: deal with special cases True and
         --    False, otherwise such literals are just constants
         --  * local variables are always references
         --  * global constants are logics in Why
         --  * global mutable variables are references
         --  * loop parameters are always mutable, and of type int

         when N_Identifier | N_Expanded_Name =>
            declare
               Id : constant W_Identifier_Id := Why_Ident_Of_Ada_Ident (Expr);
            begin
               case Ekind (Entity (Expr)) is
                  --  First treat special cases

                  when E_Enumeration_Literal =>
                     T := +Why_Expr_Of_Ada_Enum (Expr, Current_Type, EW_Prog);

                  --  There is a special case for constants introduced by
                  --  the frontend

                  when others =>
                     if Is_Mutable (Entity (Expr)) then
                        T :=
                          New_Unary_Op
                            (Ada_Node => Expr,
                             Domain   => EW_Prog,
                             Op       => EW_Deref,
                             Right    => +Id);
                     else
                        T := +Id;
                     end if;

                     if Ekind (Entity (Expr)) = E_Loop_Parameter then
                        Current_Type := Why_Int_Type;
                     end if;
               end case;
            end;

         when N_Op_Eq =>
            --  We are in a program, so we have to use boolean functions
            --  instead of predicates
            declare
               Left : constant Node_Id := Left_Opnd (Expr);
            begin
               return
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => EW_Prog,
                    Name     => Eq_Param_Name.Id (Type_Of_Node (Left)),
                    Args     =>
                      (1 => +Why_Expr_Of_Ada_Expr (Left),
                       2 => +Why_Expr_Of_Ada_Expr
                              (Right_Opnd (Expr),
                               Type_Of_Node (Left))));
            end;

         when N_Op_Minus =>
            --  unary minus
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Right);
               T :=
                 New_Unary_Op
                   (Ada_Node => Expr,
                    Domain   => EW_Prog,
                    Op       => EW_Minus,
                    Right    => +Why_Expr_Of_Ada_Expr (Right, Current_Type));
            end;

         when N_Op_Add | N_Op_Multiply | N_Op_Subtract  =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Left, Right);
               T :=
                 New_Binary_Op
                   (Ada_Node => Expr,
                    Domain   => EW_Prog,
                    Op_Type  => To_EW_Type (Current_Type.Kind),
                    Op       => Why_Binop_Of_Ada_Op (Nkind (Expr)),
                    Left     => +Why_Expr_Of_Ada_Expr (Left,
                                                       Current_Type),
                    Right    => +Why_Expr_Of_Ada_Expr (Right,
                                                       Current_Type));
               Overflow_Check_Needed := True;
            end;

         when N_Op_Divide =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Left, Right);
               T :=
                 New_Located_Call
                   (Ada_Node => Expr,
                    Name     => To_Program_Space (New_Integer_Division.Id),
                    Progs    =>
                      (1 => +Why_Expr_Of_Ada_Expr (Left,
                                                   Current_Type),
                       2 => +Why_Expr_Of_Ada_Expr (Right,
                                                   Current_Type)),
                    Reason   => VC_Division_By_Zero);
               Overflow_Check_Needed := True;
            end;

         when N_Op_Ge .. N_Op_Ne =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               return
                 New_Relation
                   (Ada_Node => Expr,
                    Domain   => EW_Prog,
                    Op       => Why_Rel_Of_Ada_Op (Nkind (Expr)),
                    Left     => +Why_Expr_Of_Ada_Expr (Left,
                                                       Base_Why_Type (Left)),
                    Right    => +Why_Expr_Of_Ada_Expr (Right,
                                                       Base_Why_Type (Right)));
            end;

         when N_Op_Not =>
            return New_Prog_Notb (Why_Expr_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Op_And =>
            return
               New_Prog_Andb
                 (Left     => Why_Expr_Of_Ada_Expr (Left_Opnd (Expr)),
                  Right    => Why_Expr_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Op_Or =>
            return
               New_Prog_Orb
                 (Left     => Why_Expr_Of_Ada_Expr (Left_Opnd (Expr)),
                  Right    => Why_Expr_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_And_Then =>
            return
               New_Prog_Andb_Then
                 (Left     => Why_Expr_Of_Ada_Expr (Left_Opnd (Expr)),
                  Right    => Why_Expr_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Or_Else =>
            return
               New_Prog_Orb_Else
                 (Left     => Why_Expr_Of_Ada_Expr (Left_Opnd (Expr)),
                  Right    => Why_Expr_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Type_Conversion =>
            --  Nothing is to do here, because we insert type conversions
            --  ourselves.
            return Why_Expr_Of_Ada_Expr (Expression (Expr), Expected_Type);

         when N_Indexed_Component =>
            --  ??? We work with single dimensional arrays for the time being
            declare
               Pre : constant Node_Id := Prefix (Expr);
            begin
               T :=
                 New_Array_Access_Prog
                  (Ada_Node      => Expr,
                   Type_Name     => Type_Of_Node (Pre),
                   Ar            => Why_Expr_Of_Ada_Expr (Pre),
                   Index         =>
                      Why_Expr_Of_Ada_Expr
                        (First (Expressions (Expr)), Why_Int_Type));
            end;

         when N_Selected_Component =>
            T :=
              New_Call
                (Domain => EW_Prog,
                 Name   =>
                   Record_Getter_Name.Id
                     (Full_Name (Entity (Selector_Name (Expr)))),
                 Args => (1 => +Why_Expr_Of_Ada_Expr (Prefix (Expr))));

         when N_Function_Call =>
            T :=
              New_Located_Call
                (Name     =>
                   To_Program_Space (Why_Ident_Of_Ada_Ident (Name (Expr))),
                 Progs    => Compute_Call_Args (Expr),
                 Ada_Node => Expr,
                 Reason   => VC_Precondition);

         when N_Expression_With_Actions =>
            return
               Sequence
                 (Why_Expr_Of_Ada_Stmts (Actions (Expr)),
                  Why_Expr_Of_Ada_Expr (Expression (Expr), Expected_Type));

         when N_Quantified_Expression =>
            --  We are interested in the checks for the entire range, and
            --  in the return value of the entire expression, but we are
            --  not interested in the exact order in which things are
            --  evaluated. We also do not want to translate the expression
            --  function by a loop. So our scheme is the following:
            --    for all I in Cond => Expr
            --
            --  becomes:
            --    (let i = ref [ int ] in
            --       if cond then ignore (expr));
            --    [ { } bool { result = true -> expr } ]
            --  The condition is a formula that expresses that i is in the
            --  range given by the quantification.
            declare
               Why_Expr   : constant W_Prog_Id :=
                              New_Ignore
                                (Prog =>
                                   Why_Expr_Of_Ada_Expr (Condition (Expr)));
               Index      : W_Identifier_Id;
               Range_Expr : Node_Id;
               Range_Cond : W_Prog_Id;
            begin
               Extract_From_Quantified_Expression (Expr, Index, Range_Expr);
               Range_Cond :=
                  Range_Prog
                    (Get_Range (Range_Expr),
                     New_Unary_Op
                       (Domain => EW_Prog,
                        Op     => EW_Deref,
                        Right  => +Index));
               return
                 Sequence
                   (New_Binding_Ref
                      (Name => Index,
                       Def  =>
                         New_Simpl_Any_Expr
                           (New_Base_Type (Base_Type => EW_Int)),
                       Context =>
                         New_Conditional
                           (Domain    => EW_Prog,
                            Condition => Range_Cond,
                            Then_Part => +Why_Expr)),
                    New_Assume_Statement
                      (Ada_Node    => Expr,
                       Return_Type => New_Base_Type (Base_Type => EW_Bool),
                       Pred        =>
                         Why_Predicate_Of_Ada_Expr (Expr)));
            end;

         when N_Attribute_Reference =>
            declare
               Aname   : constant Name_Id := Attribute_Name (Expr);
               Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
               Var     : constant Node_Id      := Prefix (Expr);
            begin
               case Attr_Id is
                  when Attribute_Result =>
                     T := +New_Identifier (Result_String);

                  when Attribute_Old =>
                     raise Not_Implemented;

                  when Attribute_First =>
                     T :=
                       New_Array_First_Prog
                         (Full_Name (Etype (Var)),
                          Why_Expr_Of_Ada_Expr (Var));
                     Current_Type := Why_Int_Type;

                  when Attribute_Last =>
                     T :=
                       New_Array_Last_Prog
                         (Full_Name (Etype (Var)),
                          Why_Expr_Of_Ada_Expr (Var));
                     Current_Type := Why_Int_Type;

                  when Attribute_Length =>
                     T :=
                       New_Array_Length_Prog
                         (Full_Name (Etype (Var)),
                          Why_Expr_Of_Ada_Expr (Var));
                     Current_Type := Why_Int_Type;

               when others =>
                  raise Not_Implemented;
               end case;
            end;

         when N_Conditional_Expression =>
            declare
               Cond      : constant Node_Id := First (Expressions (Expr));
               Then_Part : constant Node_Id := Next (Cond);
               Else_Part : constant Node_Id := Next (Then_Part);
            begin
               T :=
                  New_Conditional
                     (Ada_Node  => Expr,
                      Domain    => EW_Prog,
                      Condition => Why_Expr_Of_Ada_Expr (Cond),
                      Then_Part =>
                        +Why_Expr_Of_Ada_Expr (Then_Part, Expected_Type),
                      Else_Part =>
                        +Why_Expr_Of_Ada_Expr (Else_Part, Expected_Type));
            end;

         when N_Case_Expression =>
            T := Case_Expr_Of_Ada_Node (Expr);

         when N_Unchecked_Type_Conversion =>
            --  ??? Compiler inserted conversions are trusted
            pragma Assert (not Comes_From_Source (Expr));
            return
               Why_Expr_Of_Ada_Expr (Expression (Expr), Expected_Type);

         when N_Character_Literal =>
            --  For characters, we use their integer value
            T :=
              New_Integer_Constant
                (Ada_Node => Expr,
                 Domain   => EW_Prog,
                 Value    => Char_Literal_Value (Expr));
            Current_Type := Why_Int_Type;

         when others =>
            raise Not_Implemented;

      end case;

      declare
         Base_Type : constant Why_Type :=
            (if Overflow_Check_Needed then
               Why_Abstract (Etype (Etype (Expr)))
            else
               Why_Int_Type);
      begin
         return
           Insert_Conversion
             (Ada_Node              => Expr,
              From                  => Current_Type,
              To                    => Expected_Type,
              Why_Expr              => T,
              Base_Type => Base_Type);
      end;
   end Why_Expr_Of_Ada_Expr;

   function Why_Expr_Of_Ada_Expr (Expr : Node_Id) return W_Prog_Id is
   begin
      return Why_Expr_Of_Ada_Expr (Expr, Type_Of_Node (Expr));
   end Why_Expr_Of_Ada_Expr;

   --------------------------
   -- Int_Expr_Of_Ada_Expr --
   --------------------------

   function Int_Expr_Of_Ada_Expr (Expr : Node_Id) return W_Prog_Id is
   begin
      return Why_Expr_Of_Ada_Expr (Expr, Why_Int_Type);
   end Int_Expr_Of_Ada_Expr;

   ---------------------------
   -- Bool_Term_Of_Ada_Expr --
   ---------------------------

   function Bool_Term_Of_Ada_Expr (Expr : Node_Id) return W_Term_Id is
   begin
      return Why_Term_Of_Ada_Expr (Expr, Why_Bool_Type);
   end Bool_Term_Of_Ada_Expr;

   --------------------------
   -- Int_Term_Of_Ada_Expr --
   --------------------------

   function Int_Term_Of_Ada_Expr (Expr : Node_Id) return W_Term_Id is
   begin
      return Why_Term_Of_Ada_Expr (Expr, Why_Int_Type);
   end Int_Term_Of_Ada_Expr;

   --------------------------
   -- Why_Expr_Of_Ada_Stmt --
   --------------------------

   function Why_Expr_Of_Ada_Stmt (Stmt : Node_Id) return W_Prog_Id is
   begin
      --  ??? TBD: complete this function for the remaining cases
      case Nkind (Stmt) is
         when N_Null_Statement =>
            return New_Void (Stmt);

         when N_Assignment_Statement =>
            declare
               Lvalue : constant Node_Id := Name (Stmt);
            begin

               --  We need to differentiate the following cases
               --  * arrays
               --  * records (TBD)
               --  * simple variables

               case Nkind (Lvalue) is
                  when N_Identifier =>
                     return
                       New_Assignment
                         (Ada_Node => Stmt,
                          Name     => Why_Ident_Of_Ada_Ident (Lvalue),
                          Value    =>
                            Why_Expr_Of_Ada_Expr
                              (Expression (Stmt), Type_Of_Node (Lvalue)));

                  when N_Indexed_Component =>
                     declare
                        Pre : constant Node_Id := Prefix (Lvalue);
                     begin
                        return
                          New_Array_Update_Prog
                            (Ada_Node  => Stmt,
                             Type_Name => Type_Of_Node (Pre),
                             Ar        => Why_Ident_Of_Ada_Ident (Pre),
                             Index     =>
                               Why_Expr_Of_Ada_Expr
                                 (First (Expressions (Lvalue)), Why_Int_Type),
                             Value     =>
                               Why_Expr_Of_Ada_Expr
                                 (Expression (Stmt),
                                  Type_Of_Node
                                  (Component_Type (Etype (Pre)))));
                     end;

                  when others =>
                     raise Not_Implemented;
               end case;
            end;

         --  Translate a return statement by raising the predefined exception
         --  for returns, which is caught at the end of the subprogram. For
         --  functions, store the value returned in the local special variable
         --  for returned values, prior to raising the exception.

         when Sinfo.N_Return_Statement =>
            declare
               Raise_Stmt  : constant W_Prog_Id :=
                               New_Raise
                                 (Ada_Node => Stmt,
                                  Name     => New_Result_Exc_Identifier.Id);
               Result_Stmt : W_Prog_Id;
            begin
               if Expression (Stmt) /= Empty then
                  Result_Stmt :=
                    New_Assignment
                      (Ada_Node => Stmt,
                       Name     => New_Result_Temp_Identifier.Id,
                       Value    => Why_Expr_Of_Ada_Expr (Expression (Stmt)));
                  return Sequence (Result_Stmt, Raise_Stmt);
               else
                  return Raise_Stmt;
               end if;
            end;

         when N_Procedure_Call_Statement =>
            return
              New_Located_Call
                (Ada_Node => Stmt,
                 Name     =>
                   To_Program_Space (Why_Ident_Of_Ada_Ident (Name (Stmt))),
                 Progs    => Compute_Call_Args (Stmt),
                 Reason   => VC_Precondition);

         when N_If_Statement =>
            declare
               Tail : W_Prog_Id :=
                        Why_Expr_Of_Ada_Stmts (Else_Statements (Stmt));
            begin
               if Present (Elsif_Parts (Stmt)) then
                  declare
                     Cur : Node_Id := Last (Elsif_Parts (Stmt));
                  begin

                     --  Beginning from the tail that consists of the
                     --  translation of the Else part, possibly a no-op,
                     --  translate the list of elsif parts into a chain of
                     --  if-then-else Why expressions.

                     while Present (Cur) loop
                        Tail :=
                          New_Simpl_Conditional_Prog
                            (Condition =>
                               Why_Expr_Of_Ada_Expr (Condition (Cur)),
                             Then_Part =>
                               Why_Expr_Of_Ada_Stmts (Then_Statements (Cur)),
                             Else_Part => Tail);
                        Prev (Cur);
                     end loop;
                  end;
               end if;

               --  Finish by putting the main if-then-else on top.

               return
                 New_Simpl_Conditional_Prog
                   (Condition => Why_Expr_Of_Ada_Expr (Condition (Stmt)),
                    Then_Part =>
                      Why_Expr_Of_Ada_Stmts (Then_Statements (Stmt)),
                    Else_Part => Tail);
            end;

         when N_Raise_xxx_Error =>
            raise Not_Implemented;

         when N_Object_Declaration =>
            return Assignment_of_Obj_Decl (Stmt);

         when N_Loop_Statement =>
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
            declare
               Loop_Body    : constant List_Id := Statements (Stmt);
               Split_Node   : Node_Id;
               Invariant    : W_Predicate_Id;
               Loop_Content : W_Prog_Id;
               Scheme       : constant Node_Id := Iteration_Scheme (Stmt);
               Loop_Entity  : constant Entity_Id := Entity (Identifier (Stmt));
               Loop_Name    : constant String := Full_Name (Loop_Entity);
            begin
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
                         Condition    => New_Literal (Value => EW_True),
                         Loop_Name    => Loop_Name,
                         Invariant    => Invariant,
                         Inv_Node     => Split_Node);

               elsif
                 Nkind (Iterator_Specification (Scheme)) = N_Empty
                   and then
                 Nkind (Loop_Parameter_Specification (Scheme)) = N_Empty
               then
                  --  A while loop
                  declare
                     Enriched_Inv : constant W_Predicate_Id :=
                                      New_Simpl_Conjunction
                                        (Left  => Invariant,
                                         Right =>
                                           Why_Predicate_Of_Ada_Expr
                                             (Condition (Scheme)));
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
                          Why_Expr_Of_Ada_Expr (Condition (Scheme)),
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
                                      Get_Range
                                        (Discrete_Subtype_Definition
                                           (LParam_Spec));
                     Loop_Index   : constant String :=
                                      Full_Name
                                        (Defining_Identifier
                                           (LParam_Spec));
                     Index_Deref  : constant W_Prog_Id :=
                                      New_Unary_Op
                                        (Ada_Node => Stmt,
                                         Domain   => EW_Prog,
                                         Op       => EW_Deref,
                                         Right    =>
                                           +New_Identifier (Loop_Index));
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
                                         Name     =>
                                           New_Identifier (Loop_Index),
                                         Value    => Addition);
                     Enriched_Inv : constant W_Predicate_Id :=
                                      New_Simpl_Conjunction
                                        (Left  => Invariant,
                                         Right =>
                                           Range_Predicate
                                             (Loop_Range,
                                              New_Term (Loop_Index)));
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
                                           Range_Prog
                                             (Loop_Range,
                                              Index_Deref),
                                         Loop_Name    => Loop_Name,
                                         Invariant    => Enriched_Inv,
                                         Inv_Node     => Inv_Node);
                     Low           : constant Node_Id :=
                                       Low_Bound
                                         (Get_Range
                                           (Discrete_Subtype_Definition
                                             (LParam_Spec)));
                  begin
                     return
                       New_Binding_Ref
                         (Name    => New_Identifier (Loop_Index),
                          Def     => Int_Expr_Of_Ada_Expr (Low),
                          Context => Entire_Loop);
                  end;

               else
                  --  Some other kind of loop
                  raise Not_Implemented;
               end if;
            end;

         when N_Exit_Statement =>
            declare
               Loop_Entity : constant Entity_Id :=
                               Loop_Entity_Of_Exit_Statement (Stmt);
               Exc_Name    : constant String := Full_Name (Loop_Entity);
               Raise_Stmt  : constant W_Prog_Id :=
                               New_Raise
                                 (Ada_Node => Stmt,
                                  Name => New_Identifier (Exc_Name));
            begin
               if Nkind (Condition (Stmt)) = N_Empty then
                  return Raise_Stmt;
               else
                  return
                    New_Conditional
                      (Ada_Node  => Stmt,
                       Domain    => EW_Prog,
                       Condition =>
                          Why_Expr_Of_Ada_Expr (Condition (Stmt)),
                       Then_Part => +Raise_Stmt);
               end if;
            end;

         when N_Case_Statement =>
            return Case_Expr_Of_Ada_Node (Stmt);

         when N_Pragma =>
            case Get_Pragma_Id (Pragma_Name (Stmt)) is
               when Pragma_Annotate =>
                  return New_Void (Stmt);

               when Pragma_Check =>
                  declare
                     Arg1 : constant Node_Id :=
                              First (Pragma_Argument_Associations (Stmt));
                  begin
                     --  Pragma Check generated for Pre/Postconditions are
                     --  ignored.

                     if Chars (Get_Pragma_Arg (Arg1)) = Name_Precondition
                          or else
                        Chars (Get_Pragma_Arg (Arg1)) = Name_Postcondition
                     then
                        return New_Void (Stmt);
                     else
                        return
                          New_Located_Assert
                            (Ada_Node => Stmt,
                             Pred     => Predicate_Of_Pragma_Check (Stmt));
                     end if;
                  end;

               when others =>
                  raise Not_Implemented;
            end case;

         when others =>
            raise Not_Implemented;
      end case;
   end Why_Expr_Of_Ada_Stmt;

   ---------------------------
   -- Why_Expr_Of_Ada_Stmts --
   ---------------------------

   function Why_Expr_Of_Ada_Stmts
     (Stmts      : List_Id;
      Start_From : Node_Id := Empty)
     return W_Prog_Id
   is
      Result          : W_Prog_Id := New_Void;
      Cur_Stmt        : Node_Or_Entity_Id :=
                          (if Present (Start_From) then
                             Next (Start_From)
                           else
                             First (Stmts));
   begin
      while Present (Cur_Stmt) loop
         Result := Sequence (Result, Why_Expr_Of_Ada_Stmt (Cur_Stmt));
         Next (Cur_Stmt);
      end loop;
      return Result;
   end Why_Expr_Of_Ada_Stmts;

   ----------------------------
   -- Why_Ident_Of_Ada_Ident --
   ----------------------------

   function Why_Ident_Of_Ada_Ident (Id : Node_Id) return W_Identifier_Id
   is
      Ent : Entity_Id;
   begin
      if Nkind (Id) = N_Defining_Identifier then
         Ent := Id;
      else
         Ent := Entity (Id);
      end if;

      return New_Identifier (Full_Name (Ent));
   end Why_Ident_Of_Ada_Ident;

   -------------------------
   -- Why_Binop_Of_Ada_Op --
   -------------------------

   function Why_Binop_Of_Ada_Op (Op : N_Binary_Op) return EW_Binary_Op is
   begin
      case Op is
         when N_Op_Add      => return EW_Add;
         when N_Op_Subtract => return EW_Substract;
         when N_Op_Divide   => return EW_Divide;
         when N_Op_Multiply => return EW_Multiply;
         when N_Op_Mod      => return EW_Mod;
         when N_Op_Rem | N_Op_Concat | N_Op_Expon => raise Program_Error;
         when others => raise Program_Error;
      end case;
   end Why_Binop_Of_Ada_Op;

   -----------------------
   -- Why_Rel_Of_Ada_Op --
   -----------------------

   function Why_Rel_Of_Ada_Op (Op : N_Op_Compare) return EW_Relation is
   begin
      case Op is
         when N_Op_Gt => return EW_Gt;
         when N_Op_Lt => return EW_Lt;
         when N_Op_Eq => return EW_Eq;
         when N_Op_Ge => return EW_Ge;
         when N_Op_Le => return EW_Le;
         when N_Op_Ne => return EW_Ne;
      end case;
   end Why_Rel_Of_Ada_Op;

   -------------------------------
   -- Why_Predicate_Of_Ada_Expr --
   -------------------------------

   function Why_Predicate_Of_Ada_Expr (Expr : Node_Id) return W_Predicate_Id is
   begin
      case Nkind (Expr) is
         when N_Op_Eq |
              N_Op_Ne =>
            --  ??? Select left type as more general type for now
            return
              New_Relation
                (Ada_Node => Expr,
                 Domain   => EW_Term,
                 Left     => +Why_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    =>
                   +Why_Term_Of_Ada_Expr
                     (Right_Opnd (Expr),
                      Type_Of_Node (Left_Opnd (Expr))),
                 Op       => Why_Rel_Of_Ada_Op (Nkind (Expr)));

         when N_Op_Ge |
              N_Op_Gt |
              N_Op_Le |
              N_Op_Lt =>
            --  In Why, the builtin comparison functions expect base scalar
            --  types
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               return
                 New_Relation
                   (Ada_Node => Expr,
                    Domain   => EW_Term,
                    Left     => +Why_Term_Of_Ada_Expr (Left,
                                                      Base_Why_Type (Left)),
                    Right    => +Why_Term_Of_Ada_Expr (Right,
                                                      Base_Why_Type (Right)),
                    Op       => Why_Rel_Of_Ada_Op (Nkind (Expr)));
            end;

         when N_Op_Not =>
            return
              New_Not
                (Ada_Node => Expr,
                 Right    => +Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Op_And | N_And_Then =>
            return
              New_Simpl_Conjunction
                (Left     => Why_Predicate_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Op_Or | N_Or_Else =>
            return
              New_Connection
                (Ada_Node => Expr,
                 Domain   => EW_Pred,
                 Op       => EW_Or,
                 Left     => +Why_Predicate_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    => +Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_In =>
            if Nkind (Right_Opnd (Expr)) = N_Range then
               return
                 Range_Predicate
                   (Right_Opnd (Expr),
                    Int_Term_Of_Ada_Expr (Left_Opnd (Expr)));
            else
               raise Not_Implemented;
            end if;

         when N_Conditional_Expression =>
            declare
               Cond      : constant Node_Id := First (Expressions (Expr));
               Then_Part : constant Node_Id := Next (Cond);
               Else_Part : constant Node_Id := Next (Then_Part);
            begin
               return
                  New_Conditional_Prop
                     (Ada_Node => Expr,
                      Condition => Why_Predicate_Of_Ada_Expr (Cond),
                      Then_Part => Why_Predicate_Of_Ada_Expr (Then_Part),
                      Else_Part => Why_Predicate_Of_Ada_Expr (Else_Part));
            end;

         when N_Quantified_Expression =>
            declare
               Conclusion : constant W_Predicate_Id :=
                  Why_Predicate_Of_Ada_Expr (Condition (Expr));
               I          : W_Identifier_Id;
               Range_Expr : Node_Id;
               Hypothesis : W_Predicate_Id;
               Quant_Body : W_Predicate_Id;
            begin
               Extract_From_Quantified_Expression (Expr, I, Range_Expr);
               Hypothesis :=
                  Range_Predicate (Get_Range (Range_Expr), +I);
               Quant_Body :=
                  New_Connection
                   (Domain => EW_Pred,
                    Op     => EW_Imply,
                    Left   => +Hypothesis,
                    Right  => +Conclusion);

               if All_Present (Expr) then
                  return
                     New_Universal_Quantif
                        (Domain    => EW_Pred,
                         Ada_Node  => Expr,
                         Variables => (1 => I),
                         Var_Type  => New_Base_Type (Base_Type => EW_Int),
                         Pred      => Quant_Body);
               else
                  return
                     New_Existential_Quantif
                        (Ada_Node  => Expr,
                         Variables => (1 => I),
                         Var_Type  => New_Base_Type (Base_Type => EW_Int),
                         Pred      => Quant_Body);
               end if;
            end;

         when N_Expression_With_Actions =>

            raise Program_Error;

         when others =>
            return
              New_Relation
                (Ada_Node => Expr,
                 Domain   => EW_Term,
                 Left     => +Why_Term_Of_Ada_Expr (Expr),
                 Right    => New_Literal (Value => EW_True),
                 Op       => EW_Eq);
      end case;
   end Why_Predicate_Of_Ada_Expr;

   --------------------------
   -- Why_Term_Of_Ada_Expr --
   --------------------------

   function Why_Term_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Why_Type) return W_Term_Id
   is
      --  Here we simply analyze the structure of the Ada expression and build
      --  a corresponding Why term.
      --
      --  As for Why expressions, we may need to insert conversions, when the
      --  generated term does not have the Expected_Type. We use the local
      --  variable Current_Type to contain the type of the generated term.
      --
      --  ??? TBD: complete this function for the remaining cases
      T            : W_Term_Id;
      --  T contains the term that has been constructed before a possible
      --  conversion to or from Int
      Current_Type : Why_Type := Type_Of_Node (Expr);
   begin
      case Nkind (Expr) is
         when N_Integer_Literal =>
            T :=
              New_Integer_Constant (Ada_Node => Expr, Value => Intval (Expr));
            Current_Type := Why_Int_Type;

         when N_Real_Literal =>
            if Is_Rewrite_Substitution (Expr) then
               --  The original is usually much easier to process for alt-ergo
               --  than the rewritten node; typically, the will be in decimal
               --  base whereas the expanded node will be of the form
               --  (Num / (2 ** Den)). The division is a problem for alt-ergo,
               --  even between two litterals.
               --  However, it may happen that the original node is not
               --  in alfa, whereas the rewritten one is: typically,
               --  if the original node uses exponentiation. So try the
               --  original node and fall back to the rewritten node if
               --  failed.
               begin
                  T :=
                    Why_Term_Of_Ada_Expr (Original_Node (Expr), Why_Real_Type);
               exception
                  when Not_Implemented =>
                     T :=
                       New_Real_Constant (Ada_Node => Expr,
                                          Value    => Realval (Expr));
               end;

            else
               T :=
                 New_Real_Constant (Ada_Node => Expr, Value => Realval (Expr));
            end if;

            Current_Type := Why_Real_Type;

         when N_Character_Literal =>
            T :=
              New_Integer_Constant (Ada_Node => Expr,
                                    Value    => Char_Literal_Value (Expr));
            Current_Type := Why_Int_Type;

         when N_Identifier | N_Expanded_Name =>

            --  The corresponding Why type of the identifier may be of
            --  reference type; but here we do not care, as Why, in
            --  annotations, happily converts a reference to its base type.

            case Ekind (Entity (Expr)) is
               when E_Enumeration_Literal =>
                  T := +Why_Expr_Of_Ada_Enum (Expr, Current_Type, EW_Term);

               when others =>
                  declare
                     Id : constant W_Identifier_Id :=
                            Why_Ident_Of_Ada_Ident (Expr);
                     E  : constant Entity_Id := Entity (Expr);
                  begin
                     Current_Type := Type_Of_Node (E);

                     if Is_Mutable (E) then
                        T :=
                          New_Unary_Op
                            (Ada_Node => Expr,
                             Domain   => EW_Term,
                             Op       => EW_Deref,
                             Right    => +Id);
                     else
                        T := +Id;
                     end if;

                     if Ekind (E) = E_Loop_Parameter then
                        Current_Type := Why_Int_Type;
                     end if;
                  end;

            end case;

         when N_Op_Minus =>
            --  unary minus
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Right);
               T :=
                 New_Unary_Op
                   (Ada_Node => Expr,
                    Domain   => EW_Term,
                    Op       => EW_Minus,
                    Right    => Why_Term_Of_Ada_Expr (Right, Current_Type));
            end;

         when N_Op_Add | N_Op_Multiply | N_Op_Subtract =>
            --  The arguments of arithmetic functions have to be of base
            --  scalar types
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Left, Right);
               T :=
                 New_Binary_Op
                   (Ada_Node => Expr,
                    Domain   => EW_Term,
                    Left     => +Why_Term_Of_Ada_Expr (Left,
                                                       Current_Type),
                    Right    => +Why_Term_Of_Ada_Expr (Right,
                                                       Current_Type),
                    Op       => Why_Binop_Of_Ada_Op (Nkind (Expr)),
                    Op_Type  => To_EW_Type (Current_Type.Kind));
            end;

         when N_Op_Divide =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Left, Right);
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => EW_Term,
                    Name     => New_Division (Current_Type.Kind),
                    Args     =>
                      (1 => +Why_Term_Of_Ada_Expr (Left, Current_Type),
                       2 => +Why_Term_Of_Ada_Expr (Right, Current_Type)));
            end;

         when N_Op_Compare =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               return
                 New_Boolean_Cmp
                   (Cmp   => Why_Rel_Of_Ada_Op (Nkind (Expr)),
                    Left  => Why_Term_Of_Ada_Expr (Left,
                                                   Base_Why_Type (Left)),
                    Right => Why_Term_Of_Ada_Expr (Right,
                                                   Base_Why_Type (Right)));
            end;

         when N_Op_Not =>
            return
              New_Call
                (Ada_Node => Expr,
                 Domain   => EW_Term,
                 Name     => New_Identifier ("bool_not"),
                 Args     =>
                   (1 => +Bool_Term_Of_Ada_Expr (Right_Opnd (Expr))));

         when N_Op_And | N_And_Then =>
            return
               New_Call
                (Ada_Node => Expr,
                 Domain   => EW_Term,
                 Name     => New_Identifier ("bool_and"),
                 Args     =>
                   (1 => +Bool_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                    2 => +Bool_Term_Of_Ada_Expr (Right_Opnd (Expr))));

         when N_Op_Or | N_Or_Else =>
            return
               New_Call
                (Ada_Node => Expr,
                 Domain   => EW_Term,
                 Name     => New_Identifier ("bool_or"),
                 Args     =>
                   (1 => +Bool_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                    2 => +Bool_Term_Of_Ada_Expr (Right_Opnd (Expr))));

         when N_Type_Conversion =>
            return Why_Term_Of_Ada_Expr (Expression (Expr), Expected_Type);

         when N_Indexed_Component =>
            --  ??? We work with single dimensional arrays for the time being
            T :=
              New_Array_Access_Term
               (Type_Name => Type_Of_Node (Prefix (Expr)),
                Ar        => Why_Term_Of_Ada_Expr (Prefix (Expr)),
                Index     =>
                  Why_Term_Of_Ada_Expr
                    (First (Expressions (Expr)), Why_Int_Type));

         when N_Raise_Constraint_Error =>
            --  This means the program contains some obvious constraint error
            --  This should not happen.
            --  ??? Or maybe it can happen, and we should generate an
            --  unprovable VC?
               raise Not_Implemented;

         when N_Attribute_Reference =>
            declare
               Aname   : constant Name_Id := Attribute_Name (Expr);
               Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
               Var     : constant Node_Id      := Prefix (Expr);
            begin
               case Attr_Id is
                  when Attribute_Result =>
                     T := New_Result_Term;

                  when Attribute_Old =>
                     T := New_Old_Ident (Why_Ident_Of_Ada_Ident (Var));

                  when Attribute_First =>
                     T := New_Array_First_Term
                            (Full_Name (Etype (Var)),
                             +Why_Ident_Of_Ada_Ident (Var));
                     Current_Type := Why_Int_Type;

                  when Attribute_Last =>
                     T := New_Array_Last_Term
                            (Full_Name (Etype (Var)),
                             +Why_Ident_Of_Ada_Ident (Var));
                     Current_Type := Why_Int_Type;

                  when Attribute_Length =>
                     T := New_Array_Length_Term
                            (Full_Name (Etype (Var)),
                             +Why_Ident_Of_Ada_Ident (Var));
                     Current_Type := Why_Int_Type;

                  when others =>
                     raise Not_Implemented;

               end case;
            end;

         when N_Case_Expression =>
            --  In case expressions, we walk backwards the list of patterns
            --  and build boolean if expressions in Why.
            --  Each pattern is actually a disjunction of atoms,
            --  where an atom is either a range, a constant, an identifier or
            --  "others".
            --  For each pattern p => expr, we construct a condition c
            --  (iterating over the disjunction) from the pattern p and build
            --  the term ite (c, expr, t), where t is the term that has been
            --  obtained up to now.
            declare
               Cur_Case     : Node_Id := Last (Alternatives (Expr));
               Matched_Term : constant W_Term_Id :=
                                Int_Term_Of_Ada_Expr (Expression (Expr));
            begin
               pragma Assert (Present (Cur_Case));
               --  We initialize T to an arbitrary value
               T := Why_Term_Of_Ada_Expr
                      (Expression (Cur_Case),
                       Expected_Type);
               while Present (Cur_Case) loop
                  pragma Assert
                     (Nkind (Cur_Case) = N_Case_Expression_Alternative);
                  declare
                     Cur_Choice : Node_Id :=
                        First (Discrete_Choices (Cur_Case));
                     C : W_Term_Id := New_Literal (Value => EW_False);
                  begin
                     while Present (Cur_Choice) loop
                        C := New_Orb
                               (C,
                                Term_Equal_To (Matched_Term, Cur_Choice));
                        Next (Cur_Choice);
                     end loop;
                     T :=
                        New_Ifb
                          (Condition => C,
                           Left      =>
                              Why_Term_Of_Ada_Expr
                                (Expression (Cur_Case),
                                 Expected_Type),
                           Right     => T);
                  end;
                  Prev (Cur_Case);
               end loop;
               Current_Type := Expected_Type;
            end;
         when N_Unchecked_Type_Conversion =>
            --  We do not support unchecked conversion; Sometimes the compiler
            --  inserts one, in which case it should be OK.
            if Comes_From_Source (Expr) then
               raise Not_Alfa;
            else
               return Why_Term_Of_Ada_Expr (Expression (Expr), Expected_Type);
            end if;

         when N_Selected_Component =>
            T :=
              New_Call
                (Domain => EW_Term,
                 Name   =>
                   Record_Getter_Name.Id
                     (Full_Name (Entity (Selector_Name (Expr)))),
                 Args   => (1 => +Why_Term_Of_Ada_Expr (Prefix (Expr))));

         when N_Function_Call =>
            T :=
              New_Call
                 (Domain => EW_Term,
                  Name   =>
                    Logic_Func_Name.Id (Full_Name (Entity (Name (Expr)))),
                  Args   =>
                    Compute_Term_Args (Expr));

         when N_Expression_With_Actions =>

            raise Not_Implemented;

         when others =>
            raise Not_Implemented;
      end case;

      return
        Insert_Conversion_Term
          (Ada_Node => Expr,
           Why_Term => T,
           From     => Current_Type,
           To       => Expected_Type);
   end Why_Term_Of_Ada_Expr;

   function Why_Term_Of_Ada_Expr (Expr : Node_Id)
      return W_Term_Id
   is
   begin
      return Why_Term_Of_Ada_Expr (Expr, Type_Of_Node (Expr));
   end Why_Term_Of_Ada_Expr;

   function Wrap_Loop
      (Loop_Body : W_Prog_Id;
       Condition : W_Prog_Id;
       Loop_Name : String;
       Invariant : W_Predicate_Id;
       Inv_Node  : Node_Id)
      return W_Prog_Id
   is
      Entire_Body : constant W_Prog_Id :=
                      Sequence
                        (Loop_Body,
                         New_Conditional
                           (Domain    => EW_Prog,
                            Condition =>
                              New_Prog_Notb (Condition),
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

end Gnat2Why.Subprograms;
