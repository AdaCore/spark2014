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

with ALFA;               use ALFA;
with Atree;              use Atree;
with Einfo;              use Einfo;
with Namet;              use Namet;
with Nlists;             use Nlists;
with Sem_Eval;           use Sem_Eval;
with Sem_Util;           use Sem_Util;
with Sinfo;              use Sinfo;
with Snames;             use Snames;
with Stand;              use Stand;
with Uintp;              use Uintp;

with ALFA.Common;           use ALFA.Common;
with ALFA.Frame_Conditions; use ALFA.Frame_Conditions;

with Why;                   use Why;
with Why.Sinfo;             use Why.Sinfo;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Mutators;    use Why.Atree.Mutators;
with Why.Atree.Tables;      use Why.Atree.Tables;
with Why.Gen.Arrays;        use Why.Gen.Arrays;
with Why.Gen.Arrows;        use Why.Gen.Arrows;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Funcs;         use Why.Gen.Funcs;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Preds;         use Why.Gen.Preds;
with Why.Gen.Progs;         use Why.Gen.Progs;
with Why.Gen.Terms;         use Why.Gen.Terms;
with Why.Types;
with Why.Unchecked_Ids;     use Why.Unchecked_Ids;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Driver;       use Gnat2Why.Driver;
with Gnat2Why.Types;        use Gnat2Why.Types;

package body Gnat2Why.Subprograms is

   Result_String : constant String := "___result";
   --  The internal name for the result of an expression

   generic
      type T is private;
      type A is array (Positive range <>) of T;
      with function F (N : Node_Id) return T;
   function Map_Node_List_to_Array (List : List_Id) return A;
   --  Take a list of GNAT Node_Ids and apply the function F to each of them.
   --  Return the array that contains all the results, in the same order.

   function Case_Expr_Of_Ada_Node (N : Node_Id) return W_Prog_Id;
   --  Build Case expression of Ada Node.

   function Compute_Call_Args (Call : Node_Id) return W_Prog_Array;
   --  Compute arguments for a function call or procedure call. The node in
   --  argument must have a "Name" field and a "Parameter_Associations" field.

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

   function Get_Range (N : Node_Id) return Node_Id;
   --  Get the range of a range constraint or subtype definition.
   --  The return node is of kind N_Range

   function Insert_Conversion_Term
      (Ada_Node : Node_Id := Empty;
       To       : Why_Type;
       From     : Why_Type;
       Why_Term : W_Term_Id) return W_Term_Id;
   --  We expect Why_Expr to be of the type that corresponds to the type
   --  "From". We insert a conversion so that its type corresponds to "To".

   function Int_Expr_Of_Ada_Expr (Expr : Node_Id) return W_Prog_Id;
   --  Translate the given Ada expression to a Why expression of type "int".
   --  More precisely, call Why_Expr_Of_Ada_Expr with argument "Expected_Type"
   --  set to (Kind => Why_Int).

   function Int_Term_Of_Ada_Expr (Expr : Node_Id) return W_Term_Id;
   --  Translate the given Ada expression to a Why term of type "int".
   --  More precisely, call Why_Term_Of_Ada_Expr with argument "Expected_Type"
   --  set to (Kind => Why_Int).

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id;
   --  Return the Defining_Identifier of the loop that belongs to an exit
   --  statement.

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

   function Type_Of_Node (N : Node_Id) return String;
   --  Get the name of the type of an Ada node, as a string

   function Type_Of_Node (N : Node_Id) return Node_Id;
   --  Get the name of the type of an Ada node, as a Node_Id of Kind
   --  N_Defining_Identifier

   function Type_Of_Node (N : Node_Id) return Why_Type;
   --  Get the name of the type of an Ada node, as a Why Type

   function Why_Expr_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Why_Type) return W_Prog_Id;
   --  Translate a single Ada expression into a Why expression of the
   --  Expected_Type.
   --
   --  The translation is pretty direct for many constructs. We list the ones
   --  here for which there is something else to do.
   --  * Read access: We need to add a dereferencing operator in Why

   function Why_Expr_Of_Ada_Expr (Expr : Node_Id) return W_Prog_Id;
   --  Same as the previous function, but use the type of Expr as the expected
   --  type.

   function Why_Expr_Of_Ada_Stmts
     (Stmts      : List_Id;
      Start_from : Node_Id := Empty;
      Inner_Expr : W_Prog_Id := New_Void)
     return W_Prog_Id;
   --  Translate a list of Ada statements into a single Why expression.
   --  An empty list is translated to "void".
   --  The parameter Start_from indicates a node in the list from which the
   --  translation process is to be started. All nodes before and including
   --  Start_from are ignored.
   --  The parameter Inner_Expr represents an expression that is put at the
   --  very inner end of the statement list, in the scope of all object
   --  declarations.

   function Why_Ident_Of_Ada_Ident (Id : Node_Id) return W_Identifier_Id;
   --  Build a Why identifier out of an Ada Node.

   function Why_Prog_Binop_Of_Ada_Op (Op : N_Binary_Op) return W_Infix_Id;
   --  Convert an Ada binary operator to a Why term symbol

   function Why_Rel_Of_Ada_Op (Op : N_Op_Compare) return W_Relation_Id;
   --  Convert an Ada comparison operator to a Why relation symbol

   function Why_Term_Binop_Of_Ada_Op (Op : N_Binary_Op) return W_Arith_Op_Id;
   --  Convert an Ada binary operator to a Why term symbol

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
      Matched_Expr : constant W_Term_Id :=
         Int_Expr_Of_Ada_Expr (Expression (N));

      --  We always take the last branch as the default value
      T            : W_Prog_Id := Branch_Expr (Cur_Case);

      --  beginning of processing for Case_Expr_Of_Ada_Node
   begin
      Cur_Case := Prev (Cur_Case);

      while Present (Cur_Case) loop
         declare
            Cur_Choice : Node_Id := First (Discrete_Choices (Cur_Case));
            C : W_Prog_Id := New_Prog_Constant (Def => New_False_Literal);
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

   -----------------------
   -- Compute_Call_Args --
   -----------------------

   function Compute_Call_Args (Call : Node_Id) return W_Prog_Array
   is
      Params : constant List_Id := Parameter_Associations (Call);
      Len    : constant Nat := List_Length (Params);
   begin
      if Len = 0 then
         return (1 => New_Void (Call));
      else
         declare
            Cur_Formal : Node_Id :=
               First_Entity (Entity (Name (Call)));
            Cur_Actual : Node_Id :=
               First (Params);
            Why_Args : W_Prog_Array :=
               (1 .. Integer (Len) => Why.Types.Why_Empty);
            Cnt      : Positive := 1;
            In_Named : Boolean := False;
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
               case Ekind (Cur_Formal) is
                  when E_In_Out_Parameter | E_Out_Parameter =>
                     --  Parameters that are "out" must be variables
                     --  They are translated "as is"
                     Why_Args (Cnt) :=
                        New_Prog_Identifier
                           (Ada_Node => Cur_Actual,
                            Def      =>
                              Why_Ident_Of_Ada_Ident (Cur_Actual));

                  when others =>
                     --  No special treatment for parameters that are
                     --  not "out"
                     Why_Args (Cnt) :=
                        Why_Expr_Of_Ada_Expr
                          (Cur_Actual,
                           Type_Of_Node (Cur_Formal));
               end case;
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
               Cnt := Cnt + 1;
            end loop;
            return Why_Args;
         end;
      end if;
   end Compute_Call_Args;

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
      Pred := New_True_Literal_Pred;
      Split_Node := Empty;
      while Nkind (Cur_Stmt) /= N_Empty loop
         case Nkind (Cur_Stmt) is
            when N_If_Statement =>
               if Nkind (Original_Node (Cur_Stmt)) = N_Pragma and then
                  Get_Name_String
                    (Chars
                      (Pragma_Identifier (Original_Node (Cur_Stmt))))
                     = "assert" then
                  Pred :=
                    New_Simpl_Conjunction
                      (Left => Pred,
                       Right =>
                         New_Negation
                           (Ada_Node => Cur_Stmt,
                            Operand  =>
                              Why_Predicate_Of_Ada_Expr
                                (Condition (Cur_Stmt))));
               else
                  exit;
               end if;
            when others =>
               exit;
         end case;
         Split_Node := Cur_Stmt;
         Nlists.Next (Cur_Stmt);
      end loop;
   end Compute_Invariant;

   ---------------
   -- Get_Range --
   ---------------

   function Get_Range (N : Node_Id) return Node_Id
   is
   begin
      case Nkind (N) is
         when N_Range =>
            return N;
         when N_Subtype_Indication =>
            return Range_Expression (Constraint (N));
         when others =>
            raise Program_Error;
      end case;
   end Get_Range;

   ---------------------
   -- Range_Predicate --
   ---------------------

   function Range_Predicate (N : Node_Id; T : W_Term_Id) return W_Predicate_Id
   --  Compute a range predicate from a N_Range node.
   is
   begin
      return
        New_Related_Terms
          (Left => Int_Term_Of_Ada_Expr (Low_Bound (N)),
           Op => New_Rel_Le,
           Right => T,
           Op2 => New_Rel_Le,
           Right2 => Int_Term_Of_Ada_Expr (High_Bound (N)));
   end Range_Predicate;

   ----------------
   -- Range_Prog --
   ----------------

   function Range_Prog (N : Node_Id; T : W_Prog_Id) return W_Prog_Id
   is
   begin
      return
         New_Prog_Andb_Then
            (Left =>
              New_Infix_Call
                (Infix    => New_Op_Le_Prog,
                 Left     => Int_Expr_Of_Ada_Expr (Low_Bound (N)),
                 Right    => Duplicate_Any_Node (Id => T)),
             Right =>
              New_Infix_Call
                (Infix    => New_Op_Le_Prog,
                 Left     => T,
                 Right    => Int_Expr_Of_Ada_Expr (High_Bound (N))));
   end Range_Prog;

   ----------------------------
   -- Insert_Conversion_Term --
   ----------------------------

   function Insert_Conversion_Term
      (Ada_Node : Node_Id := Empty;
       To       : Why_Type;
       From     : Why_Type;
       Why_Term : W_Term_Id) return W_Term_Id
   is
   begin
      if To = From then
         return Why_Term;
      end if;

      if To.Kind = Why_Int or else From.Kind = Why_Int then
         return
           New_Operation
             (Ada_Node   => Ada_Node,
              Name       => Conversion_Name (From => From, To => To),
              Parameters => (1 => Why_Term));
      else
         return
            Insert_Conversion_Term
               (Ada_Node => Ada_Node,
                To       => To,
                From     => (Kind => Why_Int),
                Why_Term =>
                  Insert_Conversion_Term
                    (Ada_Node => Ada_Node,
                     To       => (Kind => Why_Int),
                     From     => From,
                     Why_Term => Why_Term));
      end if;
   end Insert_Conversion_Term;

   ----------------------------
   -- Map_Node_List_to_Array --
   ----------------------------

   function Map_Node_List_to_Array (List : List_Id) return A is
   begin
      if No (List) then
         return A'(1 .. 0 => F (Empty));
      else
         declare
            Len    : constant Pos := List_Length (List);
            Cursor : Node_Or_Entity_Id := Nlists.First (List);
            Ret    : A (1 .. Integer (Len));
            Cnt    : Integer range 0 .. Integer (Len) := 0;
         begin
            while Nkind (Cursor) /= N_Empty loop
               Cnt := Cnt + 1;
               Ret (Cnt) := F (Cursor);
               Next (Cursor);
            end loop;
            return Ret;
         end;
      end if;
   end Map_Node_List_to_Array;

   -----------------------------------
   -- Loop_Entity_Of_Exit_Statement --
   -----------------------------------

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id
   is
   begin
      --  If the name is directly in the given node, return that name
      if Present (Name (N)) then
         return Entity (Name (N));
      else
         --  Otherwise the exit statement belongs to the innermost loop, so
         --  simply go upwards (follow parent nodes) until we encounter the
         --  loop
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

   -------------------
   -- Prog_Equal_To --
   -------------------

   function Prog_Equal_To (E : W_Prog_Id; N : Node_Id) return W_Prog_Id
   is
   begin
      case Nkind (N) is
         when N_Identifier | N_Integer_Literal =>
            return
               New_Prog_Boolean_Cmp
                  (Cmp   => W_Rel_Eq,
                   Left  => E,
                   Right => Int_Expr_Of_Ada_Expr (N));

         when N_Range =>
            return
               New_Prog_Andb
                  (Left  =>
                     New_Prog_Boolean_Cmp
                        (Cmp   => W_Rel_Le,
                         Left  => Int_Expr_Of_Ada_Expr (Low_Bound (N)),
                         Right => E),
                   Right =>
                     New_Prog_Boolean_Cmp
                        (Cmp   => W_Rel_Le,
                         Left  => E,
                         Right =>
                           Int_Expr_Of_Ada_Expr (Low_Bound (N))));

         when N_Others_Choice =>
            return New_True_Literal_Prog;

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
         when N_Identifier | N_Integer_Literal =>
            return
               New_Boolean_Cmp
                  (Cmp   => W_Rel_Eq,
                   Left  => T,
                   Right => Int_Term_Of_Ada_Expr (N));
         when N_Range =>
            return
               New_Andb
                  (Left  =>
                     New_Boolean_Cmp
                        (Cmp   => W_Rel_Le,
                         Left  => Int_Term_Of_Ada_Expr (Low_Bound (N)),
                         Right => T),
                   Right =>
                     New_Boolean_Cmp
                        (Cmp   => W_Rel_Le,
                         Left  => T,
                         Right => Int_Term_Of_Ada_Expr (Low_Bound (N))));
         when N_Others_Choice =>
            return New_True_Literal;

         when others =>
            raise Not_Implemented;

      end case;
   end Term_Equal_To;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return Node_Id
   is
   begin
      return Etype (N);
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return String
   is
   begin
      return Full_Name (Type_Of_Node (N));
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return Why_Type
   is
   begin
      return (Why_Abstract, Type_Of_Node (N));
   end Type_Of_Node;

   --------------------------------
   -- Why_Decl_Of_Ada_Subprogram --
   --------------------------------

   procedure Why_Decl_Of_Ada_Subprogram
     (File : W_File_Id;
      Node : Node_Id)
   is
      --  ??? This function has to be expanded to deal with:
      --  * both functions and procedures;
      --  * procedure arguments;
      --  * return types.
      Spec        : constant Node_Id := Specification (Node);
      Name        : constant Name_Id := Chars (Defining_Unit_Name (Spec));
      Ada_Binders : constant List_Id := Parameter_Specifications (Spec);

      function Compute_Arrows return W_Arrow_Type_Id;
      --  Compute the argument types of the generated Why parameter

      function Compute_Binder (Arg : Node_Id) return W_Binder_Id;
      --  Compute a single Why function argument from a single Ada function /
      --  procedure argument; all result types are reference types.

      function Compute_Binders return W_Binder_Array;
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
      --  Compute the effects of the generated Why function

      generic
         type T is private;
         with function Basic_Value (Ada_Node : Node_Id := Empty) return T;
         with function Mapping (N : Node_Id) return T;
         with function Combine (Left, Right : T) return T;
      function Compute_Spec
         (Kind       : Name_Id;
          Located_Node : out Node_Id) return T;
      --  Compute the precondition of the generated Why functions.
      --  Pass the Kind Name_Precondition or Name_Postcondition to decide if
      --  you want the pre- or postcondition.
      --  Also output a suitable location node, if available.

      --------------------
      -- Compute_Arrows --
      --------------------

      function Compute_Arrows return W_Arrow_Type_Id is
         Res : W_Arrow_Type_Unchecked_Id;
         Arg : Node_Id;
         Id  : Node_Id;

      begin
         if Nkind (Specification (Node)) = N_Procedure_Specification then
            Res := New_Arrow_Stack (New_Type_Unit, Compute_Effects);
         else
            Res :=
               New_Arrow_Stack
                  (Why_Prog_Type_Of_Ada_Type
                    (Entity (Result_Definition (Specification (Node))), False),
                   Compute_Effects);
         end if;

         if Is_Empty_List (Ada_Binders) then
            Res := Push_Arg (Arrow    => Res,
                             Arg_Type => New_Type_Unit);

         else
            Arg := Last (Ada_Binders);
            while Present (Arg) loop
               Id := Defining_Identifier (Arg);
               Res := Push_Arg
                 (Arrow    => Res,
                  Name     =>
                    New_Identifier (Ada_Node => Id, Symbol => Chars (Id)),
                  Arg_Type =>
                    Why_Prog_Type_Of_Ada_Type (Id));
               Prev (Arg);
            end loop;
         end if;

         return Res;
      end Compute_Arrows;

      ---------------------
      -- Compute_Binder --
      ---------------------

      function Compute_Binder (Arg : Node_Id) return W_Binder_Id
      is
         Id : constant Node_Id := Defining_Identifier (Arg);
      begin
         return
           New_Binder
             (Ada_Node => Arg,
              Names =>
                (1 => New_Identifier (Ada_Node => Id, Symbol => Chars (Id))),
              Arg_Type =>
                Why_Prog_Type_Of_Ada_Type (Id));
      end Compute_Binder;

      ---------------------
      -- Compute_Binders --
      ---------------------

      function Compute_Binders return W_Binder_Array
      is
         function Binder_Map is new Map_Node_List_to_Array
           (T => W_Binder_Id, A => W_Binder_Array, F => Compute_Binder);
         L : constant Nat := List_Length (Ada_Binders);
      begin
         if L = 0 then
            --  ??? It should be checked if names generated by GNAT2Why can
            --  start with '__'
            return
              (1 => New_Binder
                      (Names    => (1 => New_Identifier ("__void_param")),
                       Arg_Type => New_Type_Unit));
         else
            return Binder_Map (Ada_Binders);
         end if;
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
                  declare
                     Lvalue    : constant Node_Id :=
                        Defining_Identifier (Cur_Decl);
                     Rexpr     : constant Node_Id := Expression (Cur_Decl);
                     Ident     : constant W_Identifier_Id :=
                        New_Identifier (Full_Name (Lvalue));
                     Rvalue    : constant W_Prog_Id :=
                        (if Present (Rexpr) then
                           Why_Expr_Of_Ada_Expr (Rexpr, Type_Of_Node (Lvalue))
                        else
                           New_Any_Expr
                              (Any_Type => New_Abstract_Type
                                 (Name =>
                                    New_Identifier (Type_Of_Node (Lvalue)))));
                  begin
                     if Comes_From_Source (Original_Node (Cur_Decl)) then
                        if Present (Rexpr) then
                           R :=
                             Sequence
                               (New_Assignment
                                  (Ada_Node => Cur_Decl,
                                   Name     => Ident,
                                   Value    => Rvalue),
                                R);
                        end if;
                     else
                        R :=
                          New_Binding_Ref
                            (Ada_Node => Cur_Decl,
                             Name     => Ident,
                             Def      => Rvalue,
                             Context  => R);
                     end if;
                  end;

               when others =>
                  null;

            end case;
            Cur_Decl := Prev (Cur_Decl);
         end loop;
         return R;
      end Compute_Context;

      ---------------------
      -- Compute_Effects --
      ---------------------

      function Compute_Effects return W_Effects_Id is
         E          : constant Entity_Id := Unique_Defining_Entity (Node);
         Read_Ids   : Id_Set.Set;
         Read_Reps  : Rep_Set.Set;
         Write_Ids  : Id_Set.Set;
         Write_Reps : Rep_Set.Set;
         Eff        : constant W_Effects_Unchecked_Id :=
            New_Unchecked_Effects;
      begin
         Get_Reads (E, Read_Ids, Read_Reps);
         Get_Writes (E, Write_Ids, Write_Reps);
         for Id of Read_Ids loop
            if Ekind (Id) /= E_Constant then
               Effects_Append_To_Reads
                  (Eff,
                   New_Identifier (Symbol => Chars (Id)));
            end if;
         end loop;

         for Id of Write_Ids loop
            Effects_Append_To_Writes
               (Eff,
                New_Identifier (Symbol => Chars (Id)));
         end loop;

         return Eff;
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
            Corr_Spec := Defining_Unit_Name (Specification (Node));
         else
            Corr_Spec := Corresponding_Spec (Node);
         end if;

         if Nkind (Corr_Spec) = N_Empty then
            return Cur_Spec;
         end if;

         PPCs := Spec_PPC_List (Corr_Spec);
         while Present (PPCs) loop
            if Pragma_Name (PPCs) = Kind then
               declare
                  Ada_Spec : constant Node_Id :=
                              Expression (First
                                          (Pragma_Argument_Associations
                                           (PPCs)));
               begin
                  if not Found_Location then
                     Located_Node := Ada_Spec;
                     Found_Location := True;
                  end if;
                  Cur_Spec :=
                     Combine
                       (Left     => Mapping (Ada_Spec),
                        Right    => Cur_Spec);
               end;
            end if;

            PPCs := Next_Pragma (PPCs);
         end loop;

         return Cur_Spec;

      end Compute_Spec;

      Ent : constant Entity_Id := Unique_Defining_Entity (Node);

      function Compute_Spec_Pred is new
         Compute_Spec
            (W_Predicate_Id,
             New_True_Literal_Pred,
             Why_Predicate_Of_Ada_Expr,
             New_Simpl_Conjunction);

      function Compute_Spec_Prog is new
         Compute_Spec
            (W_Prog_Id,
             New_True_Literal_Prog,
             Why_Expr_Of_Ada_Expr,
             New_Prog_Andb_Then);
   --  Start of processing for Why_Decl_Of_Ada_Subprogram

      Dummy_Node : Node_Id;
   begin
      --  Ignore procedures generated for postconditions

      if Ekind (Ent) = E_Procedure and then Is_Postcondition_Proc (Ent) then
         return;
      end if;

      case Nkind (Node) is
         when N_Subprogram_Body =>
            declare
               Stmts    : constant List_Id :=
                            Statements (Handled_Statement_Sequence (Node));
               Why_Stmt : constant W_Prog_Id :=
                           Why_Expr_Of_Ada_Stmts (Stmts);
               Pre      : constant W_Predicate_Id :=
                  Compute_Spec_Pred (Name_Precondition, Dummy_Node);
               Why_Body : constant W_Prog_Id :=
                  Sequence
                     (New_Ignore
                        (Prog =>
                           Compute_Spec_Prog (Name_Precondition, Dummy_Node)),
                      Sequence
                        (New_Assume_Statement (Node, Pred => Pre),
                         Compute_Context (Why_Stmt)));
               Loc_Node : Node_Id := Empty;
               Post     : constant W_Predicate_Id :=
                  Compute_Spec_Pred (Name_Postcondition, Loc_Node);
               Loc_Post : constant W_Predicate_Id :=
                  (if Present (Loc_Node) and then
                     Get_Kind (Post) /= W_True_Literal_Pred then
                      New_Located_Predicate
                        (Ada_Node => Loc_Node,
                         Pred     => Post)
                   else
                      Post);
            begin

               if Acts_As_Spec (Node) then
                  Declare_Parameter
                    (File   => File,
                     Name   => New_Identifier (Get_Name_String (Name)),
                     Arrows => Compute_Arrows,
                     Pre    => Duplicate_Any_Node (Id => Pre),
                     Post   => Duplicate_Any_Node (Id => Post));
               end if;

               New_Global_Binding
                 (File    => File,
                  Name    =>
                    New_Definition_Name (Get_Name_String (Name)),
                  Binders => Compute_Binders,
                  Post    => New_Assertion (Pred => Loc_Post),
                  Def     => Why_Body);
            end;

         when N_Subprogram_Declaration =>
            Declare_Parameter
              (File   => File,
               Name   => New_Identifier (Get_Name_String (Name)),
               Arrows => Compute_Arrows,
               Pre    => Compute_Spec_Pred (Name_Precondition, Dummy_Node),
               Post   => Compute_Spec_Pred (Name_Postcondition, Dummy_Node));

         when others =>
            raise Not_Implemented;
      end case;
   end Why_Decl_Of_Ada_Subprogram;

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
            T := New_Prog_Constant
                   (Ada_Node => Expr,
                    Def      => New_Integer_Constant
                                  (Ada_Node => Expr,
                                   Value    => Intval (Expr)));
            Current_Type := (Kind => Why_Int);

         when N_Identifier | N_Expanded_Name =>
            --  Deal with identifiers:
            --  * Enumeration literals: deal with special cases True and
            --    False, otherwise such literals are just constants
            --  * local variables are always references
            --  * global constants are logics in Why
            --  * global mutable variables are references
            --  * loop parameters are always mutable, and of type int
            declare
               Id : constant W_Identifier_Id :=
                  Why_Ident_Of_Ada_Ident (Expr);
            begin
               case Ekind (Entity (Expr)) is
                  --  First treat special cases
                  when E_Enumeration_Literal =>
                     if Entity (Expr) = Standard_True then
                        T := New_True_Literal_Prog;
                     elsif Entity (Expr) = Standard_False then
                        T := New_Prog_Constant (Def => New_False_Literal);
                     else
                        T := New_Prog_Identifier (Ada_Node => Expr, Def => Id);
                     end if;

                  when others =>
                     --  There is a special case for constants introduced by
                     --  the frontend
                     if Ekind (Entity (Expr)) = E_Constant and then not
                        (Comes_From_Source (Original_Node (Entity (Expr))))
                     then
                        T := New_Prog_Identifier
                              (Ada_Node => Expr,
                               Def      => Id);
                     elsif Is_Mutable (Entity (Expr)) then
                        T := New_Deref (Ada_Node => Expr, Ref => Id);
                     else
                        T := New_Prog_Identifier (Ada_Node => Expr, Def => Id);
                     end if;
                     if Ekind (Entity (Expr)) = E_Loop_Parameter then
                        Current_Type := (Kind => Why_Int);
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
                 New_Prog_Call
                   (Ada_Node => Expr,
                    Name     => Eq_Param_Name (Type_Of_Node (Left)),
                    Progs    =>
                      (1 => Why_Expr_Of_Ada_Expr (Left),
                       2 => Why_Expr_Of_Ada_Expr
                              (Right_Opnd (Expr),
                               Type_Of_Node (Left))));
            end;

         when N_Op_Minus =>
            --  unary minus
            T :=
               New_Prefix_Call
                  (Ada_Node => Expr,
                   Prefix   => New_Op_Minus_Prog (Ada_Node => Expr),
                   Operand  => Int_Expr_Of_Ada_Expr (Right_Opnd (Expr)));
            Current_Type := (Kind => Why_Int);

         when N_Op_Add | N_Op_Multiply | N_Op_Subtract  =>
            T :=
               New_Infix_Call
                 (Ada_Node => Expr,
                  Infix    => Why_Prog_Binop_Of_Ada_Op (Nkind (Expr)),
                  Left     => Int_Expr_Of_Ada_Expr (Left_Opnd (Expr)),
                  Right    => Int_Expr_Of_Ada_Expr (Right_Opnd (Expr)));
            Current_Type := (Kind => Why_Int);
            Overflow_Check_Needed := True;

         when N_Op_Divide =>
            T :=
               New_Located_Call
                 (Ada_Node => Expr,
                  Name     => To_Program_Space (New_Integer_Division),
                  Progs =>
                     (1 => Int_Expr_Of_Ada_Expr (Left_Opnd (Expr)),
                      2 => Int_Expr_Of_Ada_Expr (Right_Opnd (Expr))));
            Current_Type := (Kind => Why_Int);
            Overflow_Check_Needed := True;

         when N_Op_Ge .. N_Op_Ne =>
            return
              New_Infix_Call
                (Ada_Node => Expr,
                 Infix    => Why_Prog_Binop_Of_Ada_Op (Nkind (Expr)),
                 Left     => Int_Expr_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right     => Int_Expr_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Op_Not =>
            return
              New_Prefix_Call
                (Ada_Node => Expr,
                 Prefix   => New_Op_Not_Prog,
                 Operand  => Why_Expr_Of_Ada_Expr (Right_Opnd (Expr)));

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
            T :=
              New_Array_Access_Prog
               (Type_Name => Type_Of_Node (Prefix (Expr)),
                Ar        => Why_Expr_Of_Ada_Expr (Prefix (Expr)),
                Index     =>
                   Why_Expr_Of_Ada_Expr
                     (First (Expressions (Expr)),
                      Type_Of_Node (First_Index (Etype (Prefix (Expr))))));

         when N_Function_Call =>
            T :=
              New_Located_Call
                 (Name     => Why_Ident_Of_Ada_Ident (Name (Expr)),
                  Progs    => Compute_Call_Args (Expr),
                  Ada_Node => Expr);

         when N_Expression_With_Actions =>
            return
               Why_Expr_Of_Ada_Stmts
                  (Actions (Expr),
                   Inner_Expr =>
                     Why_Expr_Of_Ada_Expr (Expression (Expr), Expected_Type));

         when N_Quantified_Expression =>
            --  Quantified expressions in programs are expanded, so here we
            --  are generating code that belongs to a pre-/postcondition. We
            --  are not interested in the return value, and Why is not strong
            --  enough to reason about it. So here we generate a loop (of type
            --  unit) that simply executes the expression, and at the end
            --  we return an arbitrary boolean value.
            --  We generate Why code of the form
            --    let i = [ int] in
            --    while condition do { true }
            --       expression
            --    done ;
            --    [ bool ]
            --  A consequence is that we are less precise than dynamic
            --  execution; we always assume that the entire range of
            --  quantification is executed. In practice, this should not be a
            --  problem.
            declare
               Loop_Spec : constant Node_Id :=
                  Loop_Parameter_Specification (Expr);
               Index : constant W_Identifier_Id :=
                  New_Identifier (Full_Name (Defining_Identifier (Loop_Spec)));
               Loop_Inv : constant W_Loop_Annot_Id :=
                   New_Loop_Annot
                      (Invariant =>
                        New_Assertion (Pred => New_True_Literal_Pred));
               Loop_Body : constant W_Prog_Id :=
                  New_Ignore (Prog => Why_Expr_Of_Ada_Expr (Condition (Expr)));
               Loop_Condition : constant W_Prog_Id :=
                  Range_Prog
                    (Discrete_Subtype_Definition (Loop_Spec),
                     New_Deref
                       (Ref => Duplicate_Any_Node (Id => Index)));
            begin
               return
                  New_Binding_Ref
                    (Name => Index,
                     Def  => New_Any_Expr (Any_Type => New_Type_Int),
                     Context =>
                        Sequence
                           (New_While_Loop
                              (Condition  => Loop_Condition,
                               Annotation => Loop_Inv,
                               Loop_Content => Loop_Body),
                            New_Any_Expr (Any_Type => New_Type_Bool)));
            end;

         when N_Attribute_Reference =>
            declare
               Attr_Name : constant Name_Id := Attribute_Name (Expr);
               Var : constant Node_Id      := Prefix (Expr);
            begin
               if  Attr_Name = Name_Result then
                  T :=
                     New_Prog_Identifier
                        (Def => New_Identifier (Result_String));
               elsif Attr_Name = Name_Old then
                  raise Not_Implemented;
               elsif Attr_Name = Name_First then
                  T :=
                     New_Prog_Identifier
                        (Def =>
                           New_Integer_Constant
                              (Ada_Node => Expr,
                               Value =>
                                 Expr_Value
                                    (Low_Bound (First_Index (Etype (Var))))));
                  Current_Type := (Kind => Why_Int);
               elsif Attr_Name = Name_Last then
                  T :=
                     New_Prog_Identifier
                        (Def =>
                           New_Integer_Constant
                              (Ada_Node => Expr,
                               Value =>
                                 Expr_Value
                                    (High_Bound (First_Index (Etype (Var))))));
                  Current_Type := (Kind => Why_Int);
               else
                  raise Not_Implemented;
               end if;
            end;

         when N_Conditional_Expression =>
            declare
               Cond      : constant Node_Id := First (Expressions (Expr));
               Then_Part : constant Node_Id := Next (Cond);
               Else_Part : constant Node_Id := Next (Then_Part);
            begin
               T :=
                  New_Conditional_Prog
                     (Ada_Node => Expr,
                      Condition => Why_Expr_Of_Ada_Expr (Cond),
                      Then_Part => Why_Expr_Of_Ada_Expr (Then_Part),
                      Else_Part => Why_Expr_Of_Ada_Expr (Else_Part));
            end;

         when N_Case_Expression =>
            T := Case_Expr_Of_Ada_Node (Expr);

         when others =>
            raise Not_Implemented;

      end case;
      declare
         Base_Type : constant Why_Type :=
            (if Overflow_Check_Needed then
               (Why_Abstract, Etype (Etype (Expr)))
            else
               (Kind => Why_Int));
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

   function Why_Expr_Of_Ada_Expr (Expr : Node_Id)
      return W_Prog_Id
   is
   begin
      return Why_Expr_Of_Ada_Expr (Expr, Type_Of_Node (Expr));
   end Why_Expr_Of_Ada_Expr;

   --------------------------
   -- Int_Expr_Of_Ada_Expr --
   --------------------------

   function Int_Expr_Of_Ada_Expr (Expr : Node_Id) return W_Prog_Id
   is
   begin
      return Why_Expr_Of_Ada_Expr (Expr, (Kind => Why_Int));
   end Int_Expr_Of_Ada_Expr;

   --------------------------
   -- Int_Term_Of_Ada_Expr --
   --------------------------

   function Int_Term_Of_Ada_Expr (Expr : Node_Id) return W_Prog_Id
   is
   begin
      return Why_Term_Of_Ada_Expr (Expr, (Kind => Why_Int));
   end Int_Term_Of_Ada_Expr;

   --------------------------
   -- Why_Expr_Of_Ada_Stmt --
   --------------------------

   function Why_Expr_Of_Ada_Stmt (Stmt : Node_Id) return W_Prog_Id
   is
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
                  return
                    New_Array_Update_Prog
                      (Type_Name => Type_Of_Node (Prefix (Lvalue)),
                       Ar        => Why_Ident_Of_Ada_Ident (Prefix (Lvalue)),
                       Index     =>
                         Why_Expr_Of_Ada_Expr
                           (First (Expressions (Lvalue)),
                            Type_Of_Node
                              (First_Index (Etype (Prefix (Lvalue))))),
                       Value     =>
                         Why_Expr_Of_Ada_Expr (Expression (Stmt)));
               when others =>
                  raise Not_Implemented;
               end case;
            end;

         when Sinfo.N_Return_Statement =>
            --  ??? what to do in this case? We would need to know if we are
            --  in a procedure (translate to void or even omit) or function
            --  (just compile the returned expression)
            if Expression (Stmt) /= Empty then
               return Why_Expr_Of_Ada_Expr (Expression (Stmt));
            else
               return New_Void (Stmt);
            end if;

         when N_Procedure_Call_Statement =>
            --  Ignore calls to procedures generated for postconditions

            if Is_Postcondition_Proc (Entity (Name (Stmt))) then
               return New_Void (Stmt);
            end if;

            return
               New_Located_Call
                  (Ada_Node => Stmt,
                   Name     => Why_Ident_Of_Ada_Ident (Name (Stmt)),
                   Progs    => Compute_Call_Args (Stmt));

         when N_If_Statement =>
            return
              New_Simpl_Conditional_Prog
                (Condition => Why_Expr_Of_Ada_Expr (Condition (Stmt)),
                 Then_Part => Why_Expr_Of_Ada_Stmts (Then_Statements (Stmt)),
                 Else_Part => Why_Expr_Of_Ada_Stmts (Else_Statements (Stmt)));

         when N_Raise_xxx_Error =>
            --  Currently, we assume that this is a check inserted by the
            --  compiler, we transform it into an assert;
            --  we have to negate the condition
            return
            New_Located_Assert
              (Ada_Node => Stmt,
               Pred =>
                  New_Negation
                    (Operand =>
                       Why_Predicate_Of_Ada_Expr
                         (Condition (Stmt))));

         when N_Object_Declaration =>
            --  This has been dealt with at a higher level
            raise Program_Error;

         when N_Loop_Statement =>
            --  In general, we wrap loops in a try .. with Statement as
            --  follows:
            --
            --  (at toplevel)
            --    exception Loop_Name
            --  (in statement sequence)
            --    try
            --      loop
            --        <loop_body>
            --      done
            --    with Loop_Name -> void
            --
            --  The exception is necessary to deal with N_Exit_Statements (see
            --  also the corresponding case). The exception has to be declared
            --  at the toplevel.
            declare
               Loop_Body    : constant List_Id := Statements (Stmt);
               Split_Node   : Node_Id;
               Invariant    : W_Predicate_Id;
               Loop_Content : W_Prog_Id;
               Scheme       : constant Node_Id := Iteration_Scheme (Stmt);
               Loop_Entity  : constant Entity_Id :=
                  Entity (Identifier (Stmt));
               Loop_Name    : constant String := Full_Name (Loop_Entity);
               Entire_Loop  : W_Prog_Id;
            begin
               --  If the loop has no exit statement, we can skip the
               --  declaration of the exception.
               if Has_Exit (Loop_Entity) then
                  New_Exception
                     (Current_Why_Output_File,
                      New_Identifier (Loop_Name),
                      Why.Types.Why_Empty);
               end if;

               Compute_Invariant (Loop_Body, Invariant, Split_Node);
               Loop_Content :=
                  Why_Expr_Of_Ada_Stmts
                    (Stmts      => Loop_Body,
                     Start_from => Split_Node);

               --  We now have computed the loop invariant and the loop body.
               --  Depending on the kind of the loop (while, for, simple
               --  loop), we build a different loop in Why
               if Nkind (Scheme) = N_Empty then
                  --  No iteration scheme, we have a simple loop. Generate
                  --    while true do { <inv> } <body> done
                  Entire_Loop :=
                       New_While_Loop
                         (Ada_Node     => Stmt,
                          Condition    => New_True_Literal_Prog,
                          Annotation   =>
                            New_Loop_Annot
                               (Invariant =>
                                 New_Located_Assertion
                                    (Ada_Node => Split_Node,
                                     Pred => Invariant)),
                          Loop_Content => Loop_Content);
               elsif Nkind (Iterator_Specification (Scheme)) = N_Empty
                  and then
                     Nkind (Loop_Parameter_Specification (Scheme)) = N_Empty
               then
                  --  We are in a While loop. Generate
                  --    while <Cond> do { <inv> } <body> done
                  Entire_Loop :=
                    New_While_Loop
                      (Ada_Node     => Stmt,
                       Condition    =>
                         Why_Expr_Of_Ada_Expr (Condition (Scheme)),
                       Annotation   =>
                         New_Loop_Annot
                            (Invariant =>
                              New_Located_Assertion
                                 (Ada_Node => Split_Node, Pred => Invariant)),
                       Loop_Content => Loop_Content);
               elsif Nkind (Condition (Scheme)) = N_Empty then
                  --  We are in a For loop. Generate
                  --    let low = <low_value> in
                  --    let high = <high_value> in
                  --    <for-loop>
                  --  ??? Only increasing loops for now
                  declare
                     LParam_Spec : constant Node_Id :=
                        Loop_Parameter_Specification (Scheme);
                     Low         : constant Node_Id :=
                        Low_Bound
                          (Get_Range
                            (Discrete_Subtype_Definition (LParam_Spec)));
                     High        : constant Node_Id :=
                        High_Bound
                          (Get_Range
                            (Discrete_Subtype_Definition (LParam_Spec)));
                     Loop_Index  : constant Name_Id :=
                        Chars (Defining_Identifier (LParam_Spec));
                     Low_Name    : constant String :=
                        Loop_Name & "___low";
                     High_Name    : constant String :=
                        Loop_Name & "___high";
                  begin
                     Entire_Loop :=
                        New_Binding_Prog
                          (Name => New_Identifier (Low_Name),
                           Def  => Int_Expr_Of_Ada_Expr (Low),
                           Context =>
                             New_Binding_Prog
                               (Name => New_Identifier (High_Name),
                                Def  => Int_Expr_Of_Ada_Expr (High),
                                Context =>
                                   New_For_Loop
                                   (Ada_Node  => Stmt,
                                   Loop_Index => Loop_Index,
                                   Low        => New_Identifier (Low_Name),
                                   High       => New_Identifier (High_Name),
                                   Invariant  => Invariant,
                                   Loop_Body  => Loop_Content)));
                  end;
               else
                  --  Some other kind of loop
                  raise Not_Implemented;
               end if;
               if Has_Exit (Loop_Entity) then
                  return
                     New_Try_Block
                       (Ada_Node => Stmt,
                        Prog     => Entire_Loop,
                        Handler  =>
                           (1 =>
                              New_Handler
                                (Ada_Node => Stmt,
                                 Name     => New_Identifier (Loop_Name),
                                 Def      => New_Void)));
               else
                  return Entire_Loop;
               end if;

            end;

         when N_Exit_Statement =>
            declare
               Loop_Entity : constant Entity_Id :=
                  Loop_Entity_Of_Exit_Statement (Stmt);
               Exc_Name : constant String := Full_Name (Loop_Entity);
               Raise_Stmt : constant W_Prog_Id :=
                 New_Raise_Statement
                   (Ada_Node => Stmt,
                    Name => New_Identifier (Exc_Name));
            begin
               if Nkind (Condition (Stmt)) = N_Empty then
                  return Raise_Stmt;
               else
                  return
                    New_Conditional_Prog
                      (Ada_Node  => Stmt,
                       Condition =>
                          Why_Expr_Of_Ada_Expr (Condition (Stmt)),
                       Then_Part => Raise_Stmt);
               end if;
            end;

         when N_Case_Statement =>
            return Case_Expr_Of_Ada_Node (Stmt);

         when others =>
            raise Not_Implemented;

      end case;
   end Why_Expr_Of_Ada_Stmt;

   ---------------------------
   -- Why_Expr_Of_Ada_Stmts --
   ---------------------------

   function Why_Expr_Of_Ada_Stmts
     (Stmts      : List_Id;
      Start_from : Node_Id := Empty;
      Inner_Expr : W_Prog_Id := New_Void)
     return W_Prog_Id
   is
      Result          : W_Prog_Id := Inner_Expr;
      Cur_Stmt        : Node_Or_Entity_Id;
   begin
      --  Traverse the list of statements backwards, chaining the current
      --  statement in front of the already treated statements.
      --
      --  The reason to do it backwards is because statements can contain
      --  object declarations, such as:
      --    X : Integer := ...;
      --    <rest of statements>
      --  where x is visible in the rest of the list. In Why, this is
      --  translated as
      --    let x = ... in
      --      <rest of statements>
      --
      --  Therefore we go backwards, to have the <rest of statements> already
      --  translated.
      --
      --  The variable Result contains the already translated part.
      if List_Length (Stmts) = 0 then
         --  We return the default value
         return Result;
      end if;

      Cur_Stmt := Nlists.Last (Stmts);

      while Cur_Stmt /= Start_from and then Nkind (Cur_Stmt) /= N_Empty loop
         case Nkind (Cur_Stmt) is
            when N_Null_Statement =>
               null;

            when N_Object_Declaration =>
               --  Source objects should be defined at a global level

               if not Comes_From_Source (Original_Node (Cur_Stmt)) then
                  declare
                     Id       : constant Node_Id :=
                        Defining_Identifier (Cur_Stmt);
                     W_Id     : constant W_Identifier_Id :=
                        New_Identifier (Full_Name (Id));
                     Exp_Type : constant Why_Type :=
                        Type_Of_Node (Object_Definition (Cur_Stmt));
                     Def : constant W_Prog_Id :=
                        (if Present (Expression (Cur_Stmt)) then
                           Why_Expr_Of_Ada_Expr
                              (Expression (Cur_Stmt),
                               Exp_Type)
                        else
                           New_Any_Expr
                              (Any_Type =>
                                 New_Abstract_Type
                                    (Name =>
                                       New_Identifier
                                       (Type_Of_Node
                                          (Object_Definition (Cur_Stmt))))));
                  begin
                     case Ekind (Id) is
                        when E_Constant =>
                           Result := New_Binding_Prog
                             (Ada_Node => Cur_Stmt,
                              Name     => W_Id,
                              Def      => Def,
                              Context  => Result);
                        when others =>
                           Result := New_Binding_Ref
                             (Ada_Node => Cur_Stmt,
                              Name     => W_Id,
                              Def      => Def,
                              Context  => Result);
                     end case;
                  end;
               end if;

            when others =>
               --  For all other statements, we call Why_Expr_Of_Ada_Stmt
               --  to obtain a stmt, and build a statement sequence
               Result := Sequence (Why_Expr_Of_Ada_Stmt (Cur_Stmt), Result);
         end case;
         Cur_Stmt := Prev (Cur_Stmt);
      end loop;

      return Result;
   end Why_Expr_Of_Ada_Stmts;

   ----------------------------
   -- Why_Ident_Of_Ada_Ident --
   ----------------------------

   function Why_Ident_Of_Ada_Ident (Id : Node_Id) return W_Identifier_Id
   is
   begin
      return
         New_Identifier (Full_Name (Entity (Id)));
   end Why_Ident_Of_Ada_Ident;

   ------------------------------
   -- Why_Prog_Binop_Of_Ada_Op --
   ------------------------------

   function Why_Prog_Binop_Of_Ada_Op (Op : N_Binary_Op) return W_Infix_Id
   is
   begin
      case Op is
         when N_Op_Add => return New_Op_Add_Prog;
         when N_Op_Subtract => return New_Op_Substract_Prog;
         when N_Op_Divide => return New_Op_Divide_Prog;
         when N_Op_Multiply => return New_Op_Multiply_Prog;
         when N_Op_Mod => return New_Op_Mod_Prog;
         when N_Op_Gt => return New_Op_Gt_Prog;
         when N_Op_Lt => return New_Op_Lt_Prog;
         when N_Op_Eq => return New_Op_Eq_Prog;
         when N_Op_Ge => return New_Op_Ge_Prog;
         when N_Op_Le => return New_Op_Le_Prog;
         when N_Op_Ne => return New_Op_Ne_Prog;
         when N_Op_Rem | N_Op_Concat | N_Op_Expon => raise Program_Error;
         when others => raise Program_Error;
      end case;
   end Why_Prog_Binop_Of_Ada_Op;

   -----------------------
   -- Why_Rel_Of_Ada_Op --
   -----------------------

   function Why_Rel_Of_Ada_Op (Op : N_Op_Compare) return W_Relation_Id
   is
   begin
      case Op is
         when N_Op_Gt => return New_Rel_Gt;
         when N_Op_Lt => return New_Rel_Lt;
         when N_Op_Eq => return New_Rel_Eq;
         when N_Op_Ge => return New_Rel_Ge;
         when N_Op_Le => return New_Rel_Le;
         when N_Op_Ne => return New_Rel_Ne;
      end case;
   end Why_Rel_Of_Ada_Op;

   ------------------------------
   -- Why_Term_Binop_Of_Ada_Op --
   ------------------------------

   function Why_Term_Binop_Of_Ada_Op (Op : N_Binary_Op) return W_Arith_Op_Id
   is
   begin
      case Op is
         when N_Op_Add => return New_Op_Add;
         when N_Op_Subtract => return New_Op_Substract;
         when N_Op_Divide => return New_Op_Divide;
         when N_Op_Multiply => return New_Op_Multiply;
         when N_Op_Mod => return New_Op_Modulo;
         when N_Op_Rem | N_Op_Concat | N_Op_Expon => raise Program_Error;
         when others => raise Program_Error;
      end case;
   end Why_Term_Binop_Of_Ada_Op;

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
              New_Related_Terms
                (Ada_Node => Expr,
                 Left     => Why_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    =>
                   Why_Term_Of_Ada_Expr
                     (Right_Opnd (Expr),
                      Type_Of_Node (Left_Opnd (Expr))),
                 Op       => Why_Rel_Of_Ada_Op (Nkind (Expr)));

         when N_Op_Ge |
              N_Op_Gt |
              N_Op_Le |
              N_Op_Lt =>
            --  In Why, the builtin comparison functions expect type "int"
            return
              New_Related_Terms
                (Ada_Node => Expr,
                 Left     => Int_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    => Int_Term_Of_Ada_Expr (Right_Opnd (Expr)),
                 Op       => Why_Rel_Of_Ada_Op (Nkind (Expr)));

         when N_Op_Not =>
            return
              New_Negation
                (Ada_Node => Expr,
                 Operand  => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Op_And | N_And_Then =>
            return
              New_Simpl_Conjunction
                (Left     => Why_Predicate_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Op_Or | N_Or_Else =>
            return
              New_Disjunction
                (Ada_Node => Expr,
                 Left     => Why_Predicate_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));

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
               Quant_Spec : constant Node_Id :=
                  Loop_Parameter_Specification (Expr);
               I          : constant W_Identifier_Id :=
                  New_Identifier (Symbol =>
                     Chars (Defining_Identifier (Quant_Spec)));
               Conclusion : constant W_Predicate_Id :=
                  Why_Predicate_Of_Ada_Expr (Condition (Expr));
               Hypothesis : constant W_Predicate_Id :=
                  Range_Predicate
                     (Discrete_Subtype_Definition (Quant_Spec),
                      New_Term_Identifier (Name => I));
               Quant_Body : constant W_Predicate_Id :=
                  New_Implication
                     (Left => Hypothesis,
                      Right => Conclusion);
            begin
               if All_Present (Expr) then
                  return
                     New_Universal_Quantif
                        (Ada_Node  => Expr,
                         Variables => (1 => I),
                         Var_Type  => New_Type_Int,
                         Pred      => Quant_Body);
               else
                  return
                     New_Existential_Quantif
                        (Ada_Node  => Expr,
                         Variables => (1 => I),
                         Var_Type  => New_Type_Int,
                         Pred      => Quant_Body);
               end if;
            end;

         when N_Expression_With_Actions =>
            --  This is probably a quantifier
            return
               Why_Predicate_Of_Ada_Expr (Original_Node (Expr));

         when others =>
            return
              New_Related_Terms
                (Ada_Node => Expr,
                 Left     => Why_Term_Of_Ada_Expr (Expr),
                 Right    => New_True_Literal,
                 Op       => New_Rel_Eq);
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
      T : W_Term_Id;
      --  T contains the term that has been constructed before a possible
      --  conversion to or from Int
      Current_Type : Why_Type := Type_Of_Node (Expr);
   begin
      case Nkind (Expr) is
         when N_Integer_Literal =>
            T :=
              New_Integer_Constant (Ada_Node => Expr, Value => Intval (Expr));
            Current_Type := (Kind => Why_Int);

         when N_Identifier | N_Expanded_Name =>
            --  The corresponding Why type of the identifier may be of
            --  reference type; but here we do not care, as Why, in
            --  annotations, happily converts a reference to its base type.
            if Entity (Expr) = Standard_True then
               T := New_True_Literal;
            elsif Entity (Expr) = Standard_False then
               T := New_False_Literal;
            else
               T :=
                 New_Term_Identifier
                   (Ada_Node => Expr,
                    Name     => Why_Ident_Of_Ada_Ident (Expr));
            end if;
            if Ekind (Entity (Expr)) = E_Loop_Parameter then
               Current_Type := (Kind => Why_Int);
            end if;

         when N_Op_Add | N_Op_Multiply | N_Op_Subtract =>
            --  The arguments of arithmetic functions have to be of type int
            T :=
              New_Arith_Operation
                (Ada_Node => Expr,
                 Left     => Int_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    => Int_Term_Of_Ada_Expr (Right_Opnd (Expr)),
                 Op       => Why_Term_Binop_Of_Ada_Op (Nkind (Expr)));
            Current_Type := (Kind =>  Why_Int);
         when N_Op_Divide =>
            T :=
               New_Operation
                 (Ada_Node   => Expr,
                  Name       => New_Integer_Division,
                  Parameters =>
                    (1 => Int_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                     2 => Int_Term_Of_Ada_Expr (Right_Opnd (Expr))));
            Current_Type := (Kind =>  Why_Int);
         when N_Op_Compare =>
            return
               New_Boolean_Cmp
                  (Cmp   => Get_Kind (Why_Rel_Of_Ada_Op (Nkind (Expr))),
                   Left  => Int_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                   Right => Int_Term_Of_Ada_Expr (Right_Opnd (Expr)));

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
                    (First (Expressions (Expr)),
                     Type_Of_Node (First_Index (Etype (Prefix (Expr)))))
                  );

         when N_Raise_Constraint_Error =>
            --  This means the program contains some obvious constraint error
            --  This should not happen.
            --  ??? Or maybe it can happen, and we should generate an
            --  unprovable VC?
               raise Not_Implemented;

         when N_Attribute_Reference =>
            declare
               Attr_Name : constant Name_Id := Attribute_Name (Expr);
               Var : constant Node_Id      := Prefix (Expr);
            begin
               if  Attr_Name = Name_Result then
                  T := New_Result_Identifier;
               elsif Attr_Name = Name_Old then
                  T := New_Term_Identifier
                         (Name => Why_Ident_Of_Ada_Ident (Var),
                          Label => New_Identifier (""));
               elsif Attr_Name = Name_First then
                  --  ??? Not sure about this
                  T :=
                     New_Integer_Constant
                        (Ada_Node => Expr,
                         Value =>
                           Expr_Value
                              (Low_Bound (First_Index (Etype (Var)))));
                  Current_Type := (Kind => Why_Int);
               elsif Attr_Name = Name_Last then
                  --  ??? Not sure about this
                  T :=
                     New_Integer_Constant
                        (Ada_Node => Expr,
                         Value =>
                           Expr_Value
                              (High_Bound (First_Index (Etype (Var)))));
                  Current_Type := (Kind => Why_Int);
               else
                  raise Not_Implemented;
               end if;
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
                     C : W_Term_Id := New_False_Literal;
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

end Gnat2Why.Subprograms;
