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
with Uintp;              use Uintp;
with Why;                use Why;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Mutators; use Why.Atree.Mutators;
with Why.Gen.Arrays;     use Why.Gen.Arrays;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Funcs;      use Why.Gen.Funcs;

package body Gnat2Why.Subprograms is

   generic
      type T is private;
      type A is array (Positive range <>) of T;
      with function F (N : Node_Id) return T;
   function Map_Node_List_to_Array (List : List_Id) return A;
   --  Take a list of GNAT Node_Ids and apply the function F to each of them.
   --  Return the array that contains all the results, in the same order.

   type Exp_Type_Enum is (Why_Int, Ada_Type_Node);
   type Exp_Type (Kind : Exp_Type_Enum := Why_Int) is
      record
         case Kind is
            when Why_Int =>
               null;
            when Ada_Type_Node =>
               Ada_Type : Name_Id;
         end case;
      end record;
   --  ??? Missing doc

   function Conversion_Name
      (From : Exp_Type;
       To   : Exp_Type) return W_Identifier_Id
      with Pre =>
        (not (From = To) and then
         (From.Kind = Why_Int or else To.Kind = Why_Int));
   --  Return the name of the conversion function between the two types

   function Insert_Conversion
      (Ada_Node : Node_Id := Empty;
       To       : Exp_Type;
       From     : Exp_Type;
       Why_Expr : W_Prog_Id) return W_Prog_Id;
   --  We expect Why_Expr to be of the type that corresponds to the type
   --  "From". We insert a conversion so that its type corresponds to "To".

   function Insert_Conversion_Term
      (Ada_Node : Node_Id := Empty;
       To       : Exp_Type;
       From     : Exp_Type;
       Why_Term : W_Term_Id) return W_Term_Id;
   --  We expect Why_Expr to be of the type that corresponds to the type
   --  "From". We insert a conversion so that its type corresponds to "To".

   function Type_Of_Node (N : Node_Id) return String;
   --  Get the name of the type of an Ada node, as a string

   function Type_Of_Node (N : Node_Id) return Name_Id;
   --  Get the name of the type of an Ada node, as a Name_Id

   function Why_Expr_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Exp_Type) return W_Prog_Id;
   --  Translate a single Ada expression into a Why expression of the
   --  Expected_Type.
   --
   --  The translation is pretty direct for many constructs. We list the ones
   --  here for which there is something else to do.
   --  * Read access: We need to add a dereferencing operator in Why

   function Why_Expr_Of_Ada_Expr (Expr : Node_Id) return W_Prog_Id;
   --  Same as the previous function, but use the type of Expr as the expected
   --  type.

   function Why_Prog_Binop_Of_Ada_Op (Op : N_Binary_Op) return W_Infix_Id;
   --  Convert an Ada binary operator to a Why term symbol

   function Why_Rel_Of_Ada_Op (Op : N_Op_Compare) return W_Relation_Id;
   --  Convert an Ada comparison operator to a Why relation symbol

   function Why_Term_Binop_Of_Ada_Op (Op : N_Binary_Op) return W_Arith_Op_Id;
   --  Convert an Ada binary operator to a Why term symbol

   function Why_Term_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Exp_Type) return W_Term_Id;
   --  Translate an Ada Expression to a Why Term of the Expected_Type.

   function Why_Term_Of_Ada_Expr (Expr : Node_Id) return W_Term_Id;
   --  Same as the previous function, but use the type of Expr as the expected
   --  type.

   ---------------------
   -- Conversion_Name --
   ---------------------

   function Conversion_Name
      (From : Exp_Type;
       To   : Exp_Type) return W_Identifier_Id
   is
   begin
      case From.Kind is
         when Why_Int =>
            case To.Kind is
               when Why_Int =>
                  --  We have assumed the two arguments to be different
                  raise Program_Error;
               when Ada_Type_Node =>
                  return
                     New_Conversion_From_Int (Get_Name_String (To.Ada_Type));
            end case;
         when Ada_Type_Node =>
            case To.Kind is
               when Why_Int =>
                  return
                    New_Conversion_To_Int (Get_Name_String (From.Ada_Type));
               when Ada_Type_Node =>
                  raise Program_Error
                     with "Conversion between arbitrary types attempted";
            end case;
      end case;
   end Conversion_Name;

   -----------------------
   -- Insert_Conversion --
   -----------------------

   function Insert_Conversion
      (Ada_Node : Node_Id := Empty;
       To       : Exp_Type;
       From     : Exp_Type;
       Why_Expr : W_Prog_Id) return W_Prog_Id
   is
   begin
      if To = From then
         return Why_Expr;
      end if;

      if To.Kind = Why_Int or else From.Kind = Why_Int then
         return
           New_Prog_Call
             (Ada_Node => Ada_Node,
              Name     => Conversion_Name (From => From, To => To),
              Progs    => (1 => Why_Expr));
      else
         return
            Insert_Conversion
               (Ada_Node => Ada_Node,
                To       => To,
                From     => (Kind => Why_Int),
                Why_Expr =>
                  Insert_Conversion
                    (Ada_Node => Ada_Node,
                     To       => (Kind => Why_Int),
                     From     => From,
                     Why_Expr => Why_Expr));
      end if;
   end Insert_Conversion;

   ----------------------------
   -- Insert_Conversion_Term --
   ----------------------------

   function Insert_Conversion_Term
      (Ada_Node : Node_Id := Empty;
       To       : Exp_Type;
       From     : Exp_Type;
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

   function Map_Node_List_to_Array (List : List_Id) return A
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
            Next (Cursor);
         end loop;
         return Ret;
      end;
   end Map_Node_List_to_Array;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return Name_Id
   is
      Ent : constant Entity_Id := Etype (N);
   begin
      return Chars (Ent);
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return String
   is
   begin
      return Get_Name_String (Type_Of_Node (N));
   end Type_Of_Node;

   --------------------------------
   -- Why_Decl_of_Ada_Subprogram --
   --------------------------------

   procedure Why_Decl_of_Ada_Subprogram
     (File : W_File_Id;
      Node : Node_Id)
   is
      --  ??? This function has to be expanded to deal with:
      --  * both functions and procedures;
      --  * procedure arguments;
      --  * return types.
      Spec        : constant Node_Id := Specification (Node);
      Stmts       : constant List_Id :=
                      Statements (Handled_Statement_Sequence (Node));
      Name        : constant Name_Id := Chars (Defining_Unit_Name (Spec));
      Ada_Binders : constant List_Id := Parameter_Specifications (Spec);

      function Compute_Binder (Arg : Node_Id) return W_Binder_Id;
      --  Compute a single Why function argument from a single Ada function /
      --  procedure argument; all result types are reference types.

      function Compute_Binders return W_Binder_Array;
      --  Compute the arguments of the generated Why function;
      --  use argument (x : void) if the Ada procedure / function has no
      --  arguments.

      function Compute_Context (Initial_Body : W_Prog_Id) return W_Prog_Id;
      --  Add a "let" binding to Why body for each local variable of the
      --  procedure.

      function Compute_Spec (Kind : Name_Id) return W_Assertion_Id;
      --  Compute the precondition of the generated Why functions.
      --  Pass the Kind Name_Precondition or Name_Postcondition to decide if
      --  you want the pre- or postcondition.

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
                      (Names    => (1 => New_Identifier ("x")),
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
                     Init : W_Prog_Id;
                  begin
                     if Nkind (Expression (Cur_Decl)) /= N_Empty then
                        Init := Why_Expr_Of_Ada_Expr (Expression (Cur_Decl));
                     else
                        Init :=
                          New_Prog_Call
                           (Name  =>
                             Allocator_Name
                               (Type_Of_Node (Object_Definition (Cur_Decl))),
                            Progs =>
                              (1 =>
                                New_Prog_Constant (Def => New_Void_Literal)));
                     end if;

                     R := New_Binding_Ref
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
         PPCs      : Node_Id;
         Cur_Spec  : W_Predicate_Id := New_True_Literal_Pred;
      begin
         if Nkind (Corr_Spec) = N_Empty then
            return New_Assertion (Pred => Cur_Spec);
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
                  Cur_Spec :=
                     New_Conjonction
                       (Ada_Node => Ada_Spec,
                        Left     => Why_Predicate_Of_Ada_Expr (Ada_Spec),
                        Right    => Cur_Spec);
               end;
            end if;

            PPCs := Next_Pragma (PPCs);
         end loop;

         return New_Assertion (Pred => Cur_Spec);
      end Compute_Spec;

      Why_Body : constant W_Prog_Id :=
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
              (File    => File,
               Name    => Get_Name_String (Name),
               Binders => Compute_Binders,
               Pre     => Compute_Spec (Name_Precondition),
               Post    => Compute_Spec (Name_Postcondition),
               Def     => Why_Body);

         when others =>
            raise Not_Implemented;
      end case;
   end Why_Decl_of_Ada_Subprogram;

   --------------------------
   -- Why_Expr_Of_Ada_Expr --
   --------------------------

   function Why_Expr_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Exp_Type) return W_Prog_Id
   is
      T            : W_Prog_Id;
      Current_Type : Exp_Type := (Ada_Type_Node, Type_Of_Node (Expr));
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

         when N_Identifier =>
            T := New_Deref
                   (Ada_Node => Expr,
                    Ref      => New_Identifier
                                  (Ada_Node => Expr,
                                   Symbol   => Chars (Expr)));

         when N_Op_Eq =>
            --  We are in a program, so we have to use boolean functions
            --  instead of predicates
            declare
               Left    : constant Node_Id := Left_Opnd (Expr);
            begin
               return
                 New_Prog_Call
                   (Ada_Node => Expr,
                    Name     => Eq_Param_Name (Type_Of_Node (Left)),
                    Progs    =>
                      (1 => Why_Expr_Of_Ada_Expr (Left),
                       2 => Why_Expr_Of_Ada_Expr (Right_Opnd (Expr))));
            end;

         when N_Op_Add | N_Op_Multiply =>
            T :=
              New_Infix_Call
                (Ada_Node => Expr,
                 Infix    => Why_Prog_Binop_Of_Ada_Op (Nkind (Expr)),
                 Left     =>
                   Why_Expr_Of_Ada_Expr (Left_Opnd (Expr), (Kind => Why_Int)),
                 Right    =>
                   Why_Expr_Of_Ada_Expr
                      (Right_Opnd (Expr),
                       (Kind => Why_Int)));
            Current_Type := (Kind => Why_Int);

         when N_Op_Lt =>
            return
              New_Infix_Call
                (Ada_Node => Expr,
                 Infix    => New_Op_Lt_Prog,
                 Left     =>
                   Why_Expr_Of_Ada_Expr (Left_Opnd (Expr), (Kind => Why_Int)),
                 Right    =>
                   Why_Expr_Of_Ada_Expr
                     (Right_Opnd (Expr),
                      (Kind => Why_Int)));

         when N_Op_Not =>
            return
              New_Prefix_Call
                (Ada_Node => Expr,
                 Prefix   => New_Op_Not_Prog,
                 Operand  => Why_Expr_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Type_Conversion =>
            --  Nothing is to do here, because we insert type conversions
            --  ourselves.
            return Why_Expr_Of_Ada_Expr (Expression (Expr), Expected_Type);

         when N_Indexed_Component =>
            --  ??? We work with single dimensional arrays for the time being
            T :=
              New_Array_Access_Prog
               (Type_Name => (Get_Name_String (Type_Of_Node (Prefix (Expr)))),
                Ar        => Why_Expr_Of_Ada_Expr (Prefix (Expr)),
                Index     =>
                  Why_Expr_Of_Ada_Expr (First (Expressions (Expr))));

         when others =>
            raise Not_Implemented;
      end case;
      return
        Insert_Conversion
          (Ada_Node => Expr,
           From     => Current_Type,
           To       => Expected_Type,
           Why_Expr => T);
   end Why_Expr_Of_Ada_Expr;

   function Why_Expr_Of_Ada_Expr (Expr : Node_Id)
      return W_Prog_Id
   is
   begin
      return Why_Expr_Of_Ada_Expr (Expr, (Ada_Type_Node, Type_Of_Node (Expr)));
   end Why_Expr_Of_Ada_Expr;

   --------------------------
   -- Why_Expr_Of_Ada_Stmt --
   --------------------------

   function Why_Expr_Of_Ada_Stmt (Stmt : Node_Id) return W_Prog_Id
   is
      function Expr_Expr_Map is new Map_Node_List_to_Array
         (T => W_Prog_Id, A => W_Prog_Array, F => Why_Expr_Of_Ada_Expr);
   begin
      --  ??? TBD: complete this function for the remaining cases
      case Nkind (Stmt) is
         when N_Null_Statement =>
            return New_Prog_Constant (Stmt, New_Void_Literal);

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
                       Name     => New_Identifier (Symbol => Chars (Lvalue)),
                       Value    =>
                          Why_Expr_Of_Ada_Expr
                            (Expression (Stmt),
                             (Ada_Type_Node, Type_Of_Node (Lvalue))));

               when N_Indexed_Component =>
                  return
                    New_Array_Update_Prog
                      (Type_Name =>
                         Get_Name_String (Type_Of_Node (Prefix (Lvalue))),
                       Ar        =>
                         New_Identifier (Symbol => Chars (Prefix (Lvalue))),
                       Index     =>
                         Why_Expr_Of_Ada_Expr
                           (First (Expressions (Lvalue)),
                            (Ada_Type_Node,
                             Type_Of_Node
                               (First_Index (Etype (Prefix (Lvalue)))))),
                       Value     =>
                         Why_Expr_Of_Ada_Expr (Expression (Stmt)));
               when others =>
                  raise Not_Implemented;
               end case;
            end;

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
                 Name => New_Identifier (Symbol => Chars (Name (Stmt))),
                 Progs => Expr_Expr_Map (Parameter_Associations (Stmt)));

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
                (Ada_Node   => Stmt,
                 Assertions => (1 =>
                                  New_Assertion
                                    (Pred =>
                                       New_Negation
                                         (Operand =>
                                            Why_Predicate_Of_Ada_Expr
                                            (Condition (Stmt))))),
                 Prog       => New_Prog_Constant (Stmt, New_Void_Literal));

         when N_Object_Declaration =>
            --  This has been dealt with at a higher level
            raise Program_Error;

         when others =>
            raise Program_Error;
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
      --  The variable Result contains the already translated part. This can
      --  be one of
      --  * nothing (void), namely at the beginning of the process
      --  * a single statement, in one of the following situations:
      --    * we only have treated a single statement up to now
      --    * the last statement was an object declaration, so we grouped
      --      everything together in a <let>
      --  * a sequence of statements, in all other cases.
      --  These situations are distinguished with the variable Len. Naturally,
      --  we distinguish
      --  * Len = 0 (no statement)
      --  * Len = 1 (a single statement)
      --  * Len > 1 (a sequence of statements)

      --  The code uses the Len information to avoid building sequences of
      --  length 1.
      if List_Length (Stmts) = 0 then
         --  We return the default value, ie void
         return Result;
      else
         while Nkind (Cur_Stmt) /= N_Empty loop
            case Nkind (Cur_Stmt) is
               when N_Null_Statement =>
                  null;

               when N_Object_Declaration =>
                  if Len /= 0 then
                     Result := New_Binding_Ref
                       (Ada_Node => Cur_Stmt,
                        Name =>
                          New_Identifier
                            (Symbol =>
                               Chars (Defining_Identifier (Cur_Stmt))),
                        Def =>
                           Why_Expr_Of_Ada_Expr
                             (Expression (Cur_Stmt),
                              (Ada_Type_Node,
                               Type_Of_Node (Object_Definition (Cur_Stmt)))),
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
            return
              New_Related_Terms
                (Ada_Node => Expr,
                 Left     =>
                   Why_Term_Of_Ada_Expr (Left_Opnd (Expr), (Kind => Why_Int)),
                 Right    =>
                   Why_Term_Of_Ada_Expr (Right_Opnd (Expr), (Kind => Why_Int)),
                 Op       => Why_Rel_Of_Ada_Op (Nkind (Expr)));

         when N_Op_Not =>
            return
              New_Negation
                (Ada_Node => Expr,
                 Operand  => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Op_And | N_And_Then =>
            return
              New_Conjonction
                (Ada_Node => Expr,
                 Left     => Why_Predicate_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Op_Or | N_Or_Else =>
            return
              New_Disjonction
                (Ada_Node => Expr,
                 Left     => Why_Predicate_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_In =>
            if Nkind (Right_Opnd (Expr)) = N_Range then
               --  Generate a predicate of the form
               --  low_bound < int_of_type (x) < high_bound
               return
                 New_Related_Terms
                   (Left =>
                      Why_Term_Of_Ada_Expr
                        (Low_Bound (Right_Opnd (Expr)),
                         (Kind => Why_Int)),
                    Op => New_Rel_Le,
                    Right =>
                      Why_Term_Of_Ada_Expr
                        (Left_Opnd (Expr),
                         (Kind => Why_Int)),
                    Op2 => New_Rel_Le,
                    Right2 =>
                      Why_Term_Of_Ada_Expr
                        (High_Bound (Right_Opnd (Expr)),
                         (Kind => Why_Int)));
            else
               raise Not_Implemented;
            end if;

         when others =>
            raise Not_Implemented;
      end case;
   end Why_Predicate_Of_Ada_Expr;

   --------------------------
   -- Why_Term_Of_Ada_Expr --
   --------------------------

   function Why_Term_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Exp_Type) return W_Term_Id
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
      Current_Type : Exp_Type := (Ada_Type_Node, Type_Of_Node (Expr));
   begin
      case Nkind (Expr) is
         when N_Integer_Literal =>
            T :=
              New_Integer_Constant (Ada_Node => Expr, Value => Intval (Expr));
            Current_Type := (Kind => Why_Int);

         when N_Identifier =>
            --  The corresponding Why type of the identifier may be of
            --  reference type; but here we do not care, as Why, in
            --  annotations, happily converts a reference to its base type.
            T :=
              New_Term_Identifier
                (Ada_Node => Expr,
                 Name     => New_Identifier (Symbol => Chars (Expr)));

         when N_Op_Add | N_Op_Multiply =>
            --  The arguments of arithmetic functions have to be of type int
            T :=
              New_Arith_Operation
                (Ada_Node => Expr,
                 Left     =>
                   Why_Term_Of_Ada_Expr (Left_Opnd (Expr), (Kind => Why_Int)),
                 Right    =>
                   Why_Term_Of_Ada_Expr (Right_Opnd (Expr), (Kind => Why_Int)),
                 Op       => Why_Term_Binop_Of_Ada_Op (Nkind (Expr)));
            Current_Type := (Kind =>  Why_Int);

         when N_Op_Gt =>
            --  ??? TBD The treatment of N_Op_Gt is incorrect: we need to use
            --  a comparison function that returns bool
            --  ??? TBD respect the Expected_Type
            return
              New_Related_Terms
                (Ada_Node => Expr,
                 Left     => Why_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    => Why_Term_Of_Ada_Expr (Right_Opnd (Expr)),
                 Op       => New_Rel_Gt);

         when N_Type_Conversion =>
            return Why_Term_Of_Ada_Expr (Expression (Expr), Expected_Type);

         when N_Indexed_Component =>
            --  ??? We work with single dimensional arrays for the time being
            T :=
              New_Array_Access_Term
               (Type_Name => (Get_Name_String (Type_Of_Node (Prefix (Expr)))),
                Ar        => Why_Term_Of_Ada_Expr (Prefix (Expr)),
                Index     =>
                  Why_Term_Of_Ada_Expr
                    (First (Expressions (Expr)),
                     (Ada_Type_Node,
                      Type_Of_Node (First_Index (Etype (Prefix (Expr))))))
                  );

         when N_Raise_Constraint_Error =>
            --  This means the program contains some obvious constraint error
            --  This should not happen.
            --  ??? Or maybe it can happen, and we should generate an
            --  unprovable VC?
               raise Not_Implemented;

         when N_Attribute_Reference =>
            --  Special variables, for example "result" and "old", are
            --  represented as N_Attribute_Reference
            if Get_Name_String (Attribute_Name (Expr)) = "result" then
               T := New_Result_Identifier;
            else
               raise Not_Implemented;
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
      return Why_Term_Of_Ada_Expr (Expr, (Ada_Type_Node, Type_Of_Node (Expr)));
   end Why_Term_Of_Ada_Expr;

end Gnat2Why.Subprograms;
