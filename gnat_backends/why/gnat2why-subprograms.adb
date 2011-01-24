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

with Atree;              use Atree;
with Einfo;              use Einfo;
with Gnat2Why.Types;     use Gnat2Why.Types;
with Namet;              use Namet;
with Nlists;             use Nlists;
with Sinfo;              use Sinfo;
with Snames;             use Snames;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Mutators; use Why.Atree.Mutators;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Funcs;      use Why.Gen.Funcs;

package body Gnat2Why.Subprograms is

   ----------------------------
   -- Map_Node_List_to_Array --
   ----------------------------

   generic
      type T is private;
      type A is array (Positive range <>) of T;
      with function F (N : Node_Id) return T;
   function Map_Node_List_to_Array (List : List_Id)
      return A;
   function Map_Node_List_to_Array (List : List_Id)
      return A
   is
      --  The argument list should be non-empty
      Len : constant Pos := List_Length (List);
   begin
      declare
         Cursor : Node_Or_Entity_Id := Nlists.First (List);
         Ret    : A (1 .. Integer (Len));
         Cnt    : Integer range 0 .. Integer (Len) := 0;
      begin
         while Nkind (Cursor) /= N_Empty loop
            Cnt := Cnt + 1;
            Ret (Cnt) := F (Cursor);
            Cursor := Next (Cursor);
         end loop;
         return Ret;
      end;
   end Map_Node_List_to_Array;

   function From_Why_Int_Prog (Expr : Node_Id; Why_Expr : W_Prog_Id)
      return W_Prog_Id;
   --  convert the program Why_Expr, which is expected to be of "int" type, to
   --  the type in Why that corresponds to the type of the Ada Node Expr

   function From_Why_Int_Term (Expr : Node_Id; Why_Expr : W_Term_Id)
      return W_Term_Id;
   --  convert the term Why_Expr, which is expected to be of "int" type, to
   --  the type in Why that corresponds to the type of the Ada Node Expr

   function New_Prog_Ident (Id : Node_Id) return W_Prog_Id;
   --  build a program that consists of only one identifier

   function To_Why_Int_Prog (Expr : Node_Id; Why_Expr : W_Prog_Id)
      return W_Prog_Id;
   --  convert the program Why_Expr, which is expected to be of some type which
   --  possesses a conversion function to int, to "int" type in Why

   function To_Why_Int_Term (Expr : Node_Id; Why_Expr : W_Term_Id)
      return W_Term_Id;
   --  convert the term Why_Expr, which is expected to be of some type which
   --  possesses a conversion function to int, to "int" type in Why

   function Type_Of_Node (N : Node_Id) return String;
   --  Get the name of the type of an Ada node, as a string

   function Why_Prog_Binop_Of_Ada_Op (Op : N_Binary_Op) return W_Infix_Id;
   --  convert an Ada binary operator to a Why term symbol

   function Why_Rel_Of_Ada_Op (Op : N_Op_Compare) return W_Relation_Id;
   --  convert an Ada comparison operator to a Why relation symbol

   function Why_Term_Binop_Of_Ada_Op (Op : N_Binary_Op) return W_Arith_Op_Id;
   --  convert an Ada binary operator to a Why term symbol

   -----------------------
   -- From_Why_Int_Prog --
   -----------------------

   function From_Why_Int_Prog (Expr : Node_Id; Why_Expr : W_Prog_Id)
      return W_Prog_Id
   is
      Conv_Id : constant W_Identifier_Id :=
         New_Conversion_From_Int (Type_Of_Node (Expr));
   begin
      return
        New_Prog_Call
          (Ada_Node => Expr,
           Progs =>
             (1 => New_Prog_Identifier (Def => Conv_Id),
              2 => Why_Expr));
   end From_Why_Int_Prog;

   -----------------------
   -- From_Why_Int_Term --
   -----------------------

   function From_Why_Int_Term (Expr : Node_Id; Why_Expr : W_Term_Id)
      return W_Term_Id is
   begin
      return New_Operation
         (Ada_Node => Expr,
          Name => New_Conversion_From_Int (Type_Of_Node (Expr)),
          Parameters => (1 => Why_Expr));
   end From_Why_Int_Term;

   --------------------
   -- New_Prog_Ident --
   --------------------

   function New_Prog_Ident (Id : Node_Id) return W_Prog_Id
   is
   begin
      return
        New_Prog_Identifier
           (Ada_Node => Id,
            Def => New_Identifier (Ada_Node => Id, Symbol => Chars (Id)));
   end New_Prog_Ident;

   ---------------------
   -- To_Why_Int_Prog --
   ---------------------

   function To_Why_Int_Prog (Expr : Node_Id; Why_Expr : W_Prog_Id)
      return W_Prog_Id
   is
      Conv_Id : constant W_Identifier_Id :=
         New_Conversion_To_Int (Type_Of_Node (Expr));
   begin
      return
        New_Prog_Call
          (Ada_Node => Expr,
           Progs =>
             (1 => New_Prog_Identifier (Def => Conv_Id),
              2 => Why_Expr));
   end To_Why_Int_Prog;

   ---------------------
   -- To_Why_Int_Term --
   ---------------------

   function To_Why_Int_Term (Expr : Node_Id; Why_Expr : W_Term_Id)
      return W_Term_Id is
   begin
      return New_Operation
         (Ada_Node => Expr,
          Name => New_Conversion_To_Int (Type_Of_Node (Expr)),
          Parameters => (1 => Why_Expr));
   end To_Why_Int_Term;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return String
   is
      Ent : constant Entity_Id := Etype (N);
      Def : Node_Id;
   begin
      if Nkind (Associated_Node_For_Itype (Ent)) = N_Empty then
         Def := Ent;
      else
         Def := Defining_Identifier (Associated_Node_For_Itype (Ent));
      end if;
      return Get_Name_String (Chars (Def));
   end Type_Of_Node;

   --------------------------------
   -- Why_Decl_of_Ada_Subprogram --
   --------------------------------

   procedure Why_Decl_of_Ada_Subprogram
     (File : W_File_Id;
      Node : Node_Id)
   is
      --  ??? This function has to be expanded to deal with:
      --  * both functions and procedures
      --  * procedure arguments
      --  * return types
      Spec        : constant Node_Id := Specification (Node);
      Stmts       : constant List_Id :=
                     Statements (Handled_Statement_Sequence (Node));
      Name        : constant Name_Id := Chars (Defining_Unit_Name (Spec));
      Ada_Binders : constant List_Id := Parameter_Specifications (Spec);

      function Compute_Binder (Arg : Node_Id) return W_Binder_Id;
      --  Compute a single Why function argument from a single Ada function /
      --  procedure argument; all result types are reference types

      function Compute_Binders return W_Binder_Array;
      --  Compute the arguments of the generated Why function
      --  use argument (x : void) if the Ada procedure / function has no
      --  arguments

      function Compute_Context (Initial_Body : W_Prog_Id) return W_Prog_Id;
      --  Add a "let" binding to WhyBody for each local variable of the
      --  procedure

      function Compute_Spec (Kind : Name_Id) return W_Assertion_Id;
      --  Compute the precondition of the generated Why functions
      --  Pass the Kind Name_Precondition or Name_Postcondition to decide if
      --  you want the pre- or postcondition

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
              Arg_Type => Why_Prog_Type_of_Ada_Type (Parameter_Type (Arg)));
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
            --  ??? TBD: We should never choose variable names at random like
            --  that, beware of variable capture
            return
               (1 => New_Binder
                 (Names => (1 => New_Identifier ("x")),
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
         R : W_Prog_Id := Initial_Body;
      begin
         while Nkind (Cur_Decl) /= N_Empty loop
            case Nkind (Cur_Decl) is
               when N_Object_Declaration =>
                  declare
                     Init : W_Prog_Id;
                  begin
                     if Nkind (Expression (Cur_Decl)) /= N_Empty then
                        Init := Why_Expr_Of_Ada_Expr (Expression (Cur_Decl));
                     else
                        Init :=
                           New_Prog_Call
                           (Progs =>
                             (1 =>
                                New_Prog_Identifier
                                  (Def => Allocator_Name
                                    (Type_Of_Node
                                      (Object_Definition (Cur_Decl)))),
                              2 =>
                                New_Prog_Constant (Def => New_Void_Literal)));
                     end if;
                     R :=
                        New_Binding_Ref
                          (Ada_Node => Cur_Decl,
                           Name =>
                             New_Identifier
                               (Symbol =>
                                 Chars (Defining_Identifier (Cur_Decl))),
                           Def => Init,
                           Context => R);
                  end;
               when others => null;
            end case;
            Cur_Decl := Prev (Cur_Decl);
         end loop;
         return R;
      end Compute_Context;

      ------------------
      -- Compute_Spec --
      ------------------

      function Compute_Spec (Kind : Name_Id) return W_Assertion_Id
      is
         Corr_Spec : constant Node_Id := Corresponding_Spec (Node);
         PPCs : Node_Id;
      begin
         if Nkind (Corr_Spec) = N_Empty then
            return New_Assertion (Pred => New_True_Literal_Pred);
         end if;
         PPCs := Spec_PPC_List (Corr_Spec);
         loop
            if not Present (PPCs) then
               return New_Assertion (Pred => New_True_Literal_Pred);
            end if;
            if Pragma_Name (PPCs) = Kind then
               declare
                  Ada_Pre : constant Node_Id :=
                     Expression (First (Pragma_Argument_Associations (PPCs)));
               begin
                  return
                    New_Assertion
                      (Ada_Node => Ada_Pre, Pred =>
                       Why_Predicate_Of_Ada_Expr (Ada_Pre));
               end;
            end if;
            PPCs := Next_Pragma (PPCs);
         end loop;
      end Compute_Spec;

      WhyBody : constant W_Prog_Id :=
         Compute_Context (Why_Expr_of_Ada_Stmts (Stmts));

      --  Start of processing for Why_Decl_of_Ada_Subprogram

   begin
      --  ??? TBD deal with expression functions : transform into Why
      --  'function'
      --  ??? TBD compute a VC for the TCC of the Precondition
      case Nkind (Spec) is
         when N_Procedure_Specification | N_Function_Specification =>
            --  There really is no difference between functions and procedures
            --  from the point of view of Why
            Declare_Global_Binding
              (File => File,
               Name => Get_Name_String (Name),
               Binders => Compute_Binders,
               Pre => Compute_Spec (Name_Precondition),
               Post => Compute_Spec (Name_Postcondition),
               Def => WhyBody);
         when others => raise Program_Error;
      end case;

   end Why_Decl_of_Ada_Subprogram;

   --------------------------
   -- Why_Expr_Of_Ada_Expr --
   --------------------------

   function Why_Expr_Of_Ada_Expr
     (Expr       : Node_Id;
      Expect_Int : Boolean := False) return W_Prog_Id
   is
      T : W_Prog_Id;
   begin
      --  ??? TBD: complete this function for the remaining cases
      case Nkind (Expr) is
         when N_Integer_Literal =>
            T :=
              New_Prog_Constant
                (Ada_Node => Expr,
                 Def => New_Integer_Constant
                   (Ada_Node => Expr,
                    Value => Intval (Expr)));
            if Expect_Int then
               return T;
            else
               return From_Why_Int_Prog (Expr, T);
            end if;
         when N_Identifier =>
            T :=
              New_Deref
                (Ada_Node => Expr,
                 Ref => New_Identifier
                   (Ada_Node => Expr,
                    Symbol => Chars (Expr)));
            if Expect_Int then
               return To_Why_Int_Prog (Expr, T);
            else
               return T;
            end if;
         when N_Op_Eq =>
            --  We are in a program, so we have to use boolean functions
            --  instead of predicates
            declare
               Left    : constant Node_Id := Left_Opnd (Expr);
               Cmp_Fun : constant W_Prog_Id :=
                  New_Prog_Identifier (Def =>
                    Eq_Param_Name (Type_Of_Node (Left)));
            begin
               return
                 New_Prog_Call
                      (Ada_Node => Expr,
                       Progs =>
                         (1 => Cmp_Fun,
                          2 => Why_Expr_Of_Ada_Expr (Left),
                          3 =>  Why_Expr_Of_Ada_Expr (Right_Opnd (Expr))));
            end;
         when N_Op_Add | N_Op_Multiply =>
            T :=
              New_Infix_Call
                (Ada_Node => Expr,
                 Infix => Why_Prog_Binop_Of_Ada_Op (Nkind (Expr)),
                 Left => Why_Expr_Of_Ada_Expr (Left_Opnd (Expr), True),
                 Right => Why_Expr_Of_Ada_Expr (Right_Opnd (Expr), True));
            if Expect_Int then
               return T;
            else
               return From_Why_Int_Prog (Expr, T);
            end if;
         when N_Op_Lt =>
            return
              New_Infix_Call
                (Ada_Node => Expr,
                 Infix => New_Op_Lt_Prog,
                 Left => Why_Expr_Of_Ada_Expr (Left_Opnd (Expr), True),
                 Right => Why_Expr_Of_Ada_Expr (Right_Opnd (Expr), True));
         when N_Op_Not =>
            return
               New_Prefix_Call
                 (Ada_Node => Expr,
                  Prefix   => New_Op_Not_Prog,
                  Operand  => Why_Expr_Of_Ada_Expr (Right_Opnd (Expr)));
         when N_Type_Conversion =>
            --  ??? TBD Treat this. Sometimes this seems to be inserted but
            --  there actually is no type conversion to do
            return Why_Expr_Of_Ada_Expr (Expression (Expr), Expect_Int);
         when others => raise Program_Error;
      end case;
   end Why_Expr_Of_Ada_Expr;

   --------------------------
   -- Why_Expr_Of_Ada_Stmt --
   --------------------------

   function Why_Expr_Of_Ada_Stmt (Stmt : Node_Id) return W_Prog_Id
   is
      function Expr_Expr (Expr : Node_Id) return W_Prog_Id;
      --  This is a copy of the function Why_Expr_Of_Ada_Expr without the
      --  optional argument "Expect_Int"

      --------------------------
      -- Expr_Expr --
      --------------------------

      function Expr_Expr (Expr : Node_Id) return W_Prog_Id
      is
      begin
         return Why_Expr_Of_Ada_Expr (Expr, Expect_Int => False);
      end Expr_Expr;

      function Expr_Expr_Map is new Map_Node_List_to_Array
         (T => W_Prog_Id, A => W_Prog_Array, F => Expr_Expr);
   begin
      --  ??? TBD: complete this function for the remaining cases
      case Nkind (Stmt) is
         when N_Null_Statement =>
            return New_Prog_Constant (Stmt, New_Void_Literal);
         when N_Assignment_Statement =>
            --  ??? TBD: Here we have to be more careful if the left hand side
            --  is not a simple variable
            return
              New_Assignment
                (Ada_Node => Stmt,
                 Name => New_Identifier (Symbol => Chars (Name (Stmt))),
                 Value => Why_Expr_Of_Ada_Expr (Expression (Stmt)));
         when N_Return_Statement =>
            --  ??? what to do in this case? We would need to know if we are
            --  in a procedure (translate to void or even omit) or function
            --  (just compile the returned expression)
            if Expression (Stmt) /= Empty then
               return Why_Expr_Of_Ada_Expr (Expression (Stmt));
            else
               return
                 New_Prog_Constant (Ada_Node => Stmt, Def => New_Void_Literal);
            end if;
         when N_Procedure_Call_Statement =>
            --  Do not process calls to introduced "postcondition" functions
            if Get_Name_String (Chars (Name (Stmt))) = "_postconditions" then
               return New_Prog_Constant (Stmt, New_Void_Literal);
            end if;
            return
              New_Prog_Call
                (Ada_Node => Stmt,
                 Progs => (1 => New_Prog_Ident (Name (Stmt))) &
                             Expr_Expr_Map (Parameter_Associations (Stmt)));
         when N_If_Statement =>
            return
              New_Conditional_Prog
                (Ada_Node  => Stmt,
                 Condition => Why_Expr_Of_Ada_Expr (Condition (Stmt)),
                 Then_Part => Why_Expr_of_Ada_Stmts (Then_Statements (Stmt)),
                 Else_Part => Why_Expr_of_Ada_Stmts (Else_Statements (Stmt)));
         when N_Raise_Constraint_Error =>
            --  Currently, we assume that this is a check inserted by the
            --  compiler, we transform it into an assert;
            --  we have to negate the condition
            return
               New_Assert
                 (Ada_Node => Stmt,
                  Assertions => (1 => New_Assertion
                    (Pred =>
                      New_Negation
                        (Operand =>
                           Why_Predicate_Of_Ada_Expr (Condition (Stmt))))),
                  Prog => New_Prog_Constant (Stmt, New_Void_Literal));
         when N_Object_Declaration =>
            --  This has been dealt with at a higher level
            raise Program_Error;
         when others => raise Program_Error;
      end case;
   end Why_Expr_Of_Ada_Stmt;

   ---------------------------
   -- Why_Expr_of_Ada_Stmts --
   ---------------------------

   function Why_Expr_of_Ada_Stmts (Stmts : List_Id) return W_Prog_Id
   is
      Result   : W_Prog_Id := New_Prog_Constant (Def => New_Void_Literal);
      Cur_Stmt : Node_Or_Entity_Id := Nlists.Last (Stmts);
      Len      : Nat := 0;
   begin
      if List_Length (Stmts) = 0 then
         --  We return the default value, ie void
         return Result;
      else
         while Nkind (Cur_Stmt) /= N_Empty loop
            case Nkind (Cur_Stmt) is
               when N_Object_Declaration =>
                  if Len /= 0 then
                     Result :=
                        New_Binding_Ref
                          (Ada_Node => Cur_Stmt,
                           Name =>
                             New_Identifier
                               (Symbol =>
                                 Chars (Defining_Identifier (Cur_Stmt))),
                           Def => Why_Expr_Of_Ada_Expr (Expression (Cur_Stmt)),
                           Context => Result);
                     Len := 1;
                  else
                     --  we currently do not have a statement.
                     --  this means that an object declaration is the last
                     --  statement; we can simply ignore it
                     null;
                  end if;
               when others =>
                  --  For all other statements, we call Why_Expr_Of_Ada_Stmt
                  --  to obtain a stmt, and if necessary we build a statement
                  --  sequence
                  case Len is
                     when 0 =>
                        Result := Why_Expr_Of_Ada_Stmt (Cur_Stmt);
                     when 1 =>
                        declare
                           Seq : constant W_Prog_Id :=
                              New_Unchecked_Statement_Sequence;
                        begin
                           Statement_Sequence_Prepend_To_Statements
                             (Seq,
                              Result);
                           Statement_Sequence_Prepend_To_Statements
                             (Seq,
                              Why_Expr_Of_Ada_Stmt (Cur_Stmt));
                           Result := Seq;
                        end;
                     when others =>
                        Statement_Sequence_Prepend_To_Statements
                          (Result,
                           Why_Expr_Of_Ada_Stmt (Cur_Stmt));
                  end case;
                  Len := Len + 1;
            end case;
            Cur_Stmt := Prev (Cur_Stmt);
         end loop;
      end if;
      return Result;
   end Why_Expr_of_Ada_Stmts;

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
         when N_Op_Rem | N_Op_Concat | N_Op_Expon => raise Program_Error;
         when others => raise Program_Error;
      end case;
   end Why_Prog_Binop_Of_Ada_Op;

   ----------------------
   -- Why_Rel_Of_Ada_Op --
   ----------------------

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

   function Why_Predicate_Of_Ada_Expr (Expr : Node_Id) return W_Predicate_Id
   is
   begin
      case Nkind (Expr) is
         when N_Op_Compare =>
            --  In Why, the builtin comparison function works on type "int"
            --  only
            return New_Related_Terms
               (Ada_Node => Expr,
                Left => Why_Term_Of_Ada_Expr (Left_Opnd (Expr), True),
                Right => Why_Term_Of_Ada_Expr (Right_Opnd (Expr), True),
                Op => Why_Rel_Of_Ada_Op (Nkind (Expr)));
         when N_Op_Not =>
            return
              New_Negation
                (Ada_Node => Expr,
                 Operand => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));
         when N_Op_And | N_And_Then =>
            return
              New_Conjonction
                (Ada_Node => Expr,
                 Left => Why_Predicate_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));
         when N_Op_Or | N_Or_Else =>
            return
              New_Disjonction
                (Ada_Node => Expr,
                 Left => Why_Predicate_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));
         when N_In =>
            if Nkind (Right_Opnd (Expr)) = N_Range then
               --  Generate a predicate of the form
               --  low_bound < int_of_type (x) < high_bound
               return
                  New_Related_Terms
                    (Left =>
                       Why_Term_Of_Ada_Expr
                         (Low_Bound (Right_Opnd (Expr)),
                          Expect_Int => True),
                     Op => New_Rel_Le,
                     Right =>
                       Why_Term_Of_Ada_Expr
                         (Left_Opnd (Expr),
                          Expect_Int => True),
                     Op2 => New_Rel_Le,
                     Right2 =>
                       Why_Term_Of_Ada_Expr
                         (High_Bound (Right_Opnd (Expr)),
                          Expect_Int => True));
            else
               raise Program_Error;
            end if;
         when others => raise Program_Error;
      end case;
   end Why_Predicate_Of_Ada_Expr;

   --------------------------
   -- Why_Term_Of_Ada_Expr --
   --------------------------

   function Why_Term_Of_Ada_Expr
     (Expr : Node_Id;
      Expect_Int : Boolean := False) return W_Term_Id
   is
      --  ??? TBD: complete this function for the remaining cases
      T : W_Term_Id;
      --  T contains the term that has been constructed before a possible
      --  conversion to or from Int
   begin
      case Nkind (Expr) is
         when N_Integer_Literal =>
            T :=
              New_Integer_Constant (Ada_Node => Expr, Value => Intval (Expr));
            if Expect_Int then
               return T;
            else
               return From_Why_Int_Term (Expr, T);
            end if;
         when N_Identifier =>
            --  The corresponding Why type of the identifier may be of
            --  reference type; but here we do not care, as Why, in
            --  annotations, happily converts a reference to its base type.
            --  Also, we expect the identifier to be of a type in Why that
            --  corresponds to an Ada type, so if we want an "int", we have to
            --  convert
            T :=
              New_Term_Identifier
                 (Ada_Node => Expr,
                  Name => New_Identifier (Symbol => Chars (Expr)));
            if Expect_Int then
               return To_Why_Int_Term (Expr, T);
            else
               return T;
            end if;
         when N_Op_Add | N_Op_Multiply =>
            --  In any case, we want to use the builtin Why addition function,
            --  so here we go
            --  The arguments of "+" are of type int as well
            T :=
              New_Arith_Operation
                (Ada_Node => Expr,
                 Left  => Why_Term_Of_Ada_Expr (Left_Opnd (Expr), True),
                 Right => Why_Term_Of_Ada_Expr (Right_Opnd (Expr), True),
                 Op    => Why_Term_Binop_Of_Ada_Op (Nkind (Expr)));
            --  If we expect an int, we are done, otherwise we must insert
            --  a conversion
            if Expect_Int then
               return T;
            else
               return From_Why_Int_Term (Expr, T);
            end if;
         when N_Op_Gt =>
            --  ??? TBD The treatment of N_Op_Gt is incorrect: we need to use
            --  a comparison function that returns bool
            --  ??? TBD respect the Expect_Int setting
               return New_Related_Terms
                 (Ada_Node => Expr,
                  Left => Why_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                  Right => Why_Term_Of_Ada_Expr (Right_Opnd (Expr)),
                  Op => New_Rel_Gt);
         when N_Type_Conversion =>
            --  ??? TBD Treat this. Sometimes this seems to be inserted but
            --  there actually is no type conversion to do
            return Why_Term_Of_Ada_Expr (Expression (Expr));
         when N_Attribute_Reference =>
            --  Special variables, for example "result" and "old", are
            --  represented as N_Attribute_Reference
            if Get_Name_String (Attribute_Name (Expr)) = "result" then
               T := New_Result_Identifier;
               if Expect_Int then
                  return To_Why_Int_Term (Expr, T);
               else
                  return T;
               end if;
            end if;
            raise Program_Error;
         when others => raise Program_Error;
      end case;
   end Why_Term_Of_Ada_Expr;

end Gnat2Why.Subprograms;
