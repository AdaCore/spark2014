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
with Namet;              use Namet;
with Nlists;             use Nlists;
with Sinfo;              use Sinfo;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Funcs;      use Why.Gen.Funcs;

package body Gnat2Why.Subprograms is

   --------------------------
   -- Why_Term_Of_Ada_Expr --
   --------------------------

   function Why_Term_Of_Ada_Expr (Expr : Node_Id) return W_Term_Id
   is
      --  ??? TBD: complete this function for the remaining cases
   begin
      case Nkind (Expr) is
         when N_Integer_Literal =>
            return New_Integer_Constant (Value => Intval (Expr));
         when N_Identifier =>
            --  An identifier may or may not be of reference type; but here we
            --  do not care, as Why, in annotations, happily converts a
            --  reference to its base type.
            return New_Identifier (Symbol => Chars (Expr));
         when N_Op_Add =>
            return New_Arith_Operation
              (Left => Why_Term_Of_Ada_Expr (Left_Opnd (Expr)),
               Right => Why_Term_Of_Ada_Expr (Right_Opnd (Expr)),
               Op => New_Op_Add);
         when N_Type_Conversion =>
            --  ??? TBD Treat this. Sometimes this seems to be inserted but
            --  there actually is no type conversion to do
            return Why_Term_Of_Ada_Expr (Expression (Expr));
         when others => return New_Void_Literal;
      end case;
   end Why_Term_Of_Ada_Expr;
   --------------------------
   -- Why_Term_Of_Ada_Expr --
   --------------------------

   function Why_Expr_of_Ada_Expr (Expr : Node_Id) return W_Prog_Id
   is
      --  ??? TBD: complete this function for the remaining cases
   begin
      case Nkind (Expr) is
         when N_Integer_Literal =>
            return New_Prog_Constant
              (Def => New_Integer_Constant (Value => Intval (Expr)));
         when N_Identifier =>
            return New_Deref
              (Ref => New_Identifier (Symbol => Chars (Expr)));
         when others => raise Program_Error;
      end case;
   end Why_Expr_of_Ada_Expr;

   --------------------------
   -- Why_Expr_of_Ada_Stmt --
   --------------------------

   function Why_Expr_of_Ada_Stmt (Stmt : Node_Id) return W_Prog_Id
   is
      --  ??? TBD: complete this function for the remaining cases
   begin
      case Nkind (Stmt) is
         when N_Null_Statement =>
            return New_Prog_Constant (Def => New_Void_Literal);
         when N_Assignment_Statement =>
            --  ??? TBD: Here we have to be more careful if the left hand side
            --  is not a simple variable
            return New_Assignment
              (Name => New_Identifier (Symbol => Chars (Name (Stmt))),
               Value => Why_Expr_of_Ada_Expr (Expression (Stmt)));
         when N_Return_Statement =>
            --  ??? what to do in this case? We would need to know if we are
            --  in a procedure (translate to void or even omit) or function
            --  (just compile the returned expression)
            return New_Prog_Constant (Def => New_Void_Literal);
         when others => raise Program_Error;
      end case;
   end Why_Expr_of_Ada_Stmt;

   ---------------------------
   -- Why_Expr_of_Ada_Stmts --
   ---------------------------

   function Why_Expr_of_Ada_Stmts (Stmts : List_Id) return W_Prog_Id
   is
      L : constant Nat := List_Length (Stmts);
   begin
      if L = 0 then
         return New_Prog_Constant (Def => New_Void_Literal);
      end if;

      declare
         Cursor   : Node_Or_Entity_Id := Nlists.First (Stmts);
         Sequence : W_Prog_Array (1 .. Integer (L));
         Cnt      : Integer range 0 .. Integer (L) := 0;
      begin
         while Nkind (Cursor) /= N_Empty loop
            Cnt := Cnt + 1;
            Sequence (Cnt) := Why_Expr_of_Ada_Stmt (Cursor);
            Cursor := Next (Cursor);
         end loop;
         return New_Statement_Sequence (Statements => Sequence);
      end;
   end Why_Expr_of_Ada_Stmts;

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
      Is_Proc     : Boolean          := False;
      Spec        : constant Node_Id := Specification (Node);
      Stmts       : constant List_Id :=
         Statements (Handled_Statement_Sequence (Node));
      Name        : Name_Id;
      Ada_Binders : constant List_Id := Parameter_Specifications (Spec);

      ---------------------
      -- Compute_Binders --
      ---------------------
      function Compute_Binders return W_Binder_Array;
      --  Compute the arguments of the generated Why function
      --  use argument (x : void) if the Ada procedure / function has no
      --  arguments

      function Compute_Binders return W_Binder_Array
      is
         L : constant Nat := List_Length (Ada_Binders);
      begin
         if L = 0 then
            --  ??? TBD: We should never choose variable names at random like
            --  that, beware of variable capture
            return (1 => New_Binder
               (Names => (1 => New_Identifier ("x")),
                Arg_Type => New_Type_Unit));
         else
            declare
               Why_Binders : W_Binder_Array (1 .. Integer (L));
               Arg         : Node_Or_Entity_Id := Nlists.First (Ada_Binders);
               Cnt         : Integer range 0 .. Integer (L) := 0;
            begin
               while Nkind (Arg) /= N_Empty loop
                  Cnt := Cnt + 1;
                  Why_Binders (Cnt) :=
                     New_Binder
                       (Names =>
                         (1 => New_Identifier
                          (Symbol => Chars (Defining_Identifier (Arg)))),
                        Arg_Type =>
                          New_Ref_Type (Aliased_Type =>
                            New_Abstract_Type (Name =>
                              New_Identifier (Symbol =>
                                Chars (Parameter_Type (Arg))))));
                  Arg := Next (Arg);
               end loop;
               return Why_Binders;
            end;
         end if;
      end Compute_Binders;

   begin
      case Nkind (Spec) is
         when N_Procedure_Specification =>
            Is_Proc := True;
            Name := Chars (Defining_Unit_Name (Spec));
         when others => raise Program_Error;
      end case;

      --  ??? TBD compute the Why Pre/Post
      if Is_Proc then
         Declare_Global_Binding
           (File => File,
            Name => Get_Name_String (Name),
            Binders => Compute_Binders,
            Pre => New_Assertion (Pred => New_True_Literal_Pred),
            Post => New_Assertion (Pred => New_True_Literal_Pred),
            Def => Why_Expr_of_Ada_Stmts (Stmts));
      end if;
   end Why_Decl_of_Ada_Subprogram;

end Gnat2Why.Subprograms;
