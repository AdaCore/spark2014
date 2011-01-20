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

   function From_Why_Int (Expr : Node_Id; Why_Expr : W_Term_Id)
      return W_Term_Id;
   --  convert the term Why_Expr, which is expected to be of "int" type, to
   --  the type in Why that corresponds to the type of the Ada Node Expr

   function To_Why_Int (Expr : Node_Id; Why_Expr : W_Term_Id)
      return W_Term_Id;
   --  convert the term Why_Expr, which is expected to be of some type which
   --  possesses a conversion function to int, to "int" type in Why

   function New_Prog_Ident (Id : Node_Id) return W_Prog_Id;
   --  build a program that consists of only one identifier

   ------------------
   -- From_Why_Int --
   ------------------

   function From_Why_Int (Expr : Node_Id; Why_Expr : W_Term_Id)
      return W_Term_Id is
   begin
      return New_Operation
         (Ada_Node => Expr,
          Name => New_Conversion_From_Int
            (Get_Name_String (Chars (Etype (Expr)))),
          Parameters => (1 => Why_Expr));
   end From_Why_Int;

   ------------------
   -- To_Why_Int --
   ------------------

   function To_Why_Int (Expr : Node_Id; Why_Expr : W_Term_Id)
      return W_Term_Id is
   begin
      return New_Operation
         (Ada_Node => Expr,
          Name => New_Conversion_To_Int
            (Get_Name_String (Chars (Etype (Expr)))),
          Parameters => (1 => Why_Expr));
   end To_Why_Int;

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

      function Compute_Pre return W_Assertion_Id;
      --  Compute the precondition of the generated Why functions

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

      -----------------
      -- Compute_Pre --
      -----------------

      function Compute_Pre return W_Assertion_Id
      is
         PPCs : Node_Id := Spec_PPC_List (Corresponding_Spec (Node));
      begin
         loop
            if not Present (PPCs) then
               return New_Assertion (Pred => New_True_Literal_Pred);
            end if;
            if Pragma_Name (PPCs) = Name_Precondition then
               declare
                  Ada_Pre : constant Node_Id :=
                     Expression (First (Pragma_Argument_Associations (PPCs)));
               begin
                  return
                    New_Assertion
                      (Ada_Node => Ada_Pre, Pred =>
                       Why_Predicate_of_Ada_Expr (Ada_Pre));
               end;
            end if;
            PPCs := Next_Pragma (PPCs);
         end loop;
      end Compute_Pre;

   begin
      --  ??? TBD deal with expression functions : transform into Why
      --  'function'
      --  ??? TBD compute the Why Pre/Post
      --  ??? TBD compute a VC for the TCC of the Precondition
      case Nkind (Spec) is
         when N_Procedure_Specification | N_Function_Specification =>
            --  There really is no difference between functions and procedures
            --  from the point of view of Why
            Declare_Global_Binding
              (File => File,
               Name => Get_Name_String (Name),
               Binders => Compute_Binders,
               Pre => Compute_Pre,
               Post => New_Assertion (Pred => New_True_Literal_Pred),
               Def => Why_Expr_of_Ada_Stmts (Stmts));
         when others => raise Program_Error;
      end case;

   end Why_Decl_of_Ada_Subprogram;

   --------------------------
   -- Why_Expr_of_Ada_Expr --
   --------------------------

   function Why_Expr_of_Ada_Expr (Expr : Node_Id) return W_Prog_Id
   is
      --  ??? TBD: complete this function for the remaining cases
   begin
      case Nkind (Expr) is
         when N_Integer_Literal =>
            return
              New_Prog_Constant
                (Ada_Node => Expr,
                 Def => New_Integer_Constant
                   (Ada_Node => Expr,
                    Value => Intval (Expr)));
         when N_Identifier =>
            return
              New_Deref
                (Ada_Node => Expr,
                 Ref => New_Identifier
                   (Ada_Node => Expr,
                    Symbol => Chars (Expr)));
         when others => raise Program_Error;
      end case;
   end Why_Expr_of_Ada_Expr;

   --------------------------
   -- Why_Expr_of_Ada_Stmt --
   --------------------------

   function Why_Expr_of_Ada_Stmt (Stmt : Node_Id) return W_Prog_Id
   is
      --  ??? TBD: complete this function for the remaining cases
      --  ??? TBD: don't forget the corresponding Ada node
      function Expr_Expr_Map is new Map_Node_List_to_Array
         (T => W_Prog_Id, A => W_Prog_Array, F => Why_Expr_of_Ada_Expr);
   begin
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
                 Value => Why_Expr_of_Ada_Expr (Expression (Stmt)));
         when N_Return_Statement =>
            --  ??? what to do in this case? We would need to know if we are
            --  in a procedure (translate to void or even omit) or function
            --  (just compile the returned expression)
            if Expression (Stmt) /= Empty then
               return Why_Expr_of_Ada_Expr (Expression (Stmt));
            else
               return
                 New_Prog_Constant (Ada_Node => Stmt, Def => New_Void_Literal);
            end if;
         when N_Procedure_Call_Statement =>
            --  Do not process calls to introduced "postcondition functions
            if Get_Name_String (Chars (Name (Stmt))) = "_postconditions" then
               return New_Prog_Constant (Stmt, New_Void_Literal);
            end if;
            return
              New_Prog_Call
                (Ada_Node => Stmt,
                 Progs => (1 => New_Prog_Ident (Name (Stmt))) &
                             Expr_Expr_Map (Parameter_Associations (Stmt)));
         when others => raise Program_Error;
      end case;
   end Why_Expr_of_Ada_Stmt;

   ---------------------------
   -- Why_Expr_of_Ada_Stmts --
   ---------------------------

   function Why_Expr_of_Ada_Stmts (Stmts : List_Id) return W_Prog_Id
   is
      function Expr_Stmt_Map is new Map_Node_List_to_Array
         (T => W_Prog_Id, A => W_Prog_Array, F => Why_Expr_of_Ada_Stmt);
   begin
      if List_Length (Stmts) = 0 then
         return New_Prog_Constant (Def => New_Void_Literal);
      else
         return New_Statement_Sequence (Statements => Expr_Stmt_Map (Stmts));
      end if;
   end Why_Expr_of_Ada_Stmts;

   function Why_Predicate_of_Ada_Expr (Expr : Node_Id) return W_Predicate_Id
   is
   begin
      case Nkind (Expr) is
         when N_Op_Gt =>
            --  In Why, the builtin comparison function works on type "int"
            --  only
            return New_Related_Terms
               (Ada_Node => Expr,
                Left => Why_Term_Of_Ada_Expr (Left_Opnd (Expr), True),
                Right => Why_Term_Of_Ada_Expr (Right_Opnd (Expr), True),
                Op => New_Rel_Gt);
         when others => raise Program_Error;
      end case;
   end Why_Predicate_of_Ada_Expr;

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
               return From_Why_Int (Expr, T);
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
               return To_Why_Int (Expr, T);
            else
               return T;
            end if;
         when N_Op_Add =>
            --  In any case, we want to use the builtin Why addition function,
            --  so here we go
            --  The arguments of "+" are of type int as well
            T :=
              New_Arith_Operation
                (Ada_Node => Expr,
                 Left  => Why_Term_Of_Ada_Expr (Left_Opnd (Expr), True),
                 Right => Why_Term_Of_Ada_Expr (Right_Opnd (Expr), True),
                 Op    => New_Op_Add);
            --  If we expect an int, we are done, otherwise we must insert
            --  a conversion
            if Expect_Int then
               return T;
            else
               return From_Why_Int (Expr, T);
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
         when others => raise Program_Error;
      end case;
   end Why_Term_Of_Ada_Expr;

end Gnat2Why.Subprograms;
