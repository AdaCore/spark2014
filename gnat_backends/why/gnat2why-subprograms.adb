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
with Sinfo;              use Sinfo;
with Snames;             use Snames;
with Stand;              use Stand;
with Uintp;              use Uintp;

with ALFA.Frame_Conditions; use ALFA.Frame_Conditions;

with Why;                   use Why;
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
with Why.Types;
with Why.Unchecked_Ids;     use Why.Unchecked_Ids;

with Gnat2Why.Types;        use Gnat2Why.Types;
with Gnat2Why.Decls;        use Gnat2Why.Decls;

package body Gnat2Why.Subprograms is

   generic
      type T is private;
      type A is array (Positive range <>) of T;
      with function F (N : Node_Id) return T;
   function Map_Node_List_to_Array (List : List_Id) return A;
   --  Take a list of GNAT Node_Ids and apply the function F to each of them.
   --  Return the array that contains all the results, in the same order.

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

   function Type_Of_Node (N : Node_Id) return String;
   --  Get the name of the type of an Ada node, as a string

   function Type_Of_Node (N : Node_Id) return Name_Id;
   --  Get the name of the type of an Ada node, as a Name_Id

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
      Start_from : Node_Id := Empty)
     return W_Prog_Id;
   --  Translate a list of Ada statements into a single Why expression.
   --  An empty list is translated to "void".
   --  The parameter Start_from indicates a node in the list from which the
   --  translation process is to be started. All nodes before and including
   --  Start_from are ignored.

   function Why_Ident_Of_Ada_Ident (Id : Node_Id) return W_Identifier_Id;
   --  Build a Why identifier out of an Ada Node.

   function Why_Prog_Binop_Of_Ada_Op (Op : N_Binary_Op) return W_Infix_Id;
   --  Convert an Ada binary operator to a Why term symbol

   function Why_Rel_Of_Ada_Op (Op : N_Op_Compare) return W_Relation_Id;
   --  Convert an Ada comparison operator to a Why relation symbol

   function Why_Term_Binop_Of_Ada_Op (Op : N_Binary_Op) return W_Arith_Op_Id;
   --  Convert an Ada binary operator to a Why term symbol

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
                    New_Conjunction
                      (Ada_Node => Cur_Stmt,
                       Left => Pred,
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
      if Nkind (Split_Node) /= N_Empty then
         Pred :=
            New_Located_Predicate
              (Ada_Node => Split_Node,
               Pred     => Pred);
      end if;
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

      function Compute_Spec
         (Kind       : Name_Id;
          With_Label : Boolean := False) return W_Predicate_Id;
      --  Compute the precondition of the generated Why functions.
      --  Pass the Kind Name_Precondition or Name_Postcondition to decide if
      --  you want the pre- or postcondition.
      --  Generate a label only if With_Label is True.

      function Initial_Assertions
        (Initial_Body : W_Prog_Id;
         Pre          : W_Predicate_Id)
         return W_Prog_Id;
      --  Add a "precondition of precondition" to the body of the subprogram,
      --  as follows. Given Ada subprogram F with Pre P and Post Q, and
      --  translation of body B, generate the new body
      --    <asserts corresponding to precondition P>
      --    <assume P>
      --    <B>
      --    <asserts corresponding to postcondition Q>

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
                  if Comes_From_Source (Original_Node (Cur_Decl)) then
                     if Present (Expression (Cur_Decl)) then
                        declare
                           Lvalue : constant Node_Id :=
                                      Defining_Identifier (Cur_Decl);
                           Assign : W_Prog_Id;
                        begin
                           Assign :=
                             New_Assignment
                               (Ada_Node => Cur_Decl,
                                Name     =>
                                  New_Identifier (Full_Name (Lvalue)),
                                Value    =>
                                  Why_Expr_Of_Ada_Expr
                                    (Expression (Cur_Decl),
                                     (Why_Abstract,
                                      Type_Of_Node (Lvalue))));
                           R := Sequence (Assign, R);
                        end;
                     end if;
                  else
                     declare
                        Init : W_Prog_Id;
                     begin
                        if Nkind (Expression (Cur_Decl)) /= N_Empty then
                           Init :=
                              Why_Expr_Of_Ada_Expr (Expression (Cur_Decl));
                        else
                           Init :=
                             New_Prog_Call
                              (Name  =>
                                Allocator_Name
                                  (Type_Of_Node
                                     (Object_Definition (Cur_Decl))),
                               Progs => (1 => New_Void));
                        end if;
                        R := New_Binding_Ref
                          (Ada_Node => Cur_Decl,
                           Name     =>
                             New_Identifier
                               (Symbol =>
                                    Chars (Defining_Identifier (Cur_Decl))),
                           Def      => Init,
                           Context  => R);
                     end;
                  end if;
               when others => null;
            end case;
            Cur_Decl := Prev (Cur_Decl);
         end loop;
         return R;
      end Compute_Context;

      ---------------------
      -- Compute_Effects --
      ---------------------

      function Compute_Effects return W_Effects_Id is
         E          : constant Entity_Id := Get_Unique_Entity_For_Decl (Node);
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
          With_Label : Boolean := False) return W_Predicate_Id
      is
         Corr_Spec      : Node_Id;
         Cur_Spec       : W_Predicate_Id := New_True_Literal_Pred;
         Found_Location : Boolean := False;
         Located_Node   : Node_Id := Empty;
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
                     New_Conjunction
                       (Ada_Node => Ada_Spec,
                        Left     => Why_Predicate_Of_Ada_Expr (Ada_Spec),
                        Right    => Cur_Spec);
               end;
            end if;

            PPCs := Next_Pragma (PPCs);
         end loop;

         if With_Label and then Nkind (Located_Node) /= N_Empty then
            return
              New_Located_Predicate
                (Ada_Node => Located_Node,
                 Pred     => Cur_Spec);
         else
            return Cur_Spec;
         end if;
      end Compute_Spec;

      ------------------------
      -- Initial_Assertions --
      ------------------------

      function Initial_Assertions
        (Initial_Body : W_Prog_Id;
         Pre          : W_Predicate_Id)
         return W_Prog_Id
      is
         Cur_Decl : Node_Id := Last (Declarations (Node));
         Cur_Body : W_Prog_Id :=
            Sequence
               (New_Assume_Statement (Ada_Node => Cur_Decl, Pred => Pre),
                Initial_Body);
      begin
         while Nkind (Cur_Decl) /= N_Empty loop
            if Nkind (Cur_Decl) = N_Raise_Constraint_Error then
               declare
                  Pred : constant W_Predicate_Id :=
                     New_Negation (Operand =>
                        Why_Predicate_Of_Ada_Expr (Condition (Cur_Decl)));
               begin
                  Cur_Body :=
                     Sequence
                        (New_Located_Assert
                           (Ada_Node => Cur_Decl,
                            Pred => Pred),
                         Cur_Body);
               end;
            end if;
            Prev (Cur_Decl);
         end loop;
         return Cur_Body;
      end Initial_Assertions;

      Ent : constant Entity_Id := Get_Unique_Entity_For_Decl (Node);

   --  Start of processing for Why_Decl_of_Ada_Subprogram

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
                  Compute_Spec (Name_Precondition);
               Why_Body : constant W_Prog_Id :=
                            Initial_Assertions
                              (Compute_Context (Why_Stmt),
                               Pre);
            begin
               --  ??? TBD deal with expression functions : transform into Why
               --  'function'
               --  ??? TBD compute a VC for the TCC of the Precondition
               --  We fix "true" as precondition and assume the precondition
               --  in the subprogram body
               New_Global_Binding
                 (File    => File,
                  Name    =>
                    New_Definition_Name (Get_Name_String (Name)),
                  Binders => Compute_Binders,
                  Post    =>
                    New_Assertion
                       (Pred =>
                        Compute_Spec
                           (Kind       => Name_Postcondition,
                            With_Label => True)),
                  Def     => Why_Body);
            end;

         when N_Subprogram_Declaration =>
            Declare_Parameter
              (File   => File,
               Name   => New_Identifier (Get_Name_String (Name)),
               Arrows => Compute_Arrows,
               Pre    => Compute_Spec (Name_Precondition),
               Post   => Compute_Spec (Name_Postcondition));

         when others =>
            raise Not_Implemented;
      end case;
   end Why_Decl_of_Ada_Subprogram;

   --------------------------
   -- Why_Expr_Of_Ada_Expr --
   --------------------------

   function Why_Expr_Of_Ada_Expr
     (Expr          : Node_Id;
      Expected_Type : Why_Type) return W_Prog_Id
   is
      T            : W_Prog_Id;
      Current_Type : Why_Type := (Why_Abstract, Type_Of_Node (Expr));
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
            --  Deal with identifiers:
            --  * Enumeration literals: deal with special cases True and
            --    False, otherwise such literals are just constants
            --  * local variables are always references
            --  * global constants are logics in Why
            --  * global mutable variables are references
            --  * loop parameters are always mutable, and of type int
            case Ekind (Entity (Expr)) is
               --  First treat special cases
               when E_Enumeration_Literal =>
                  if Entity (Expr) = Standard_True then
                     T := New_Prog_Constant (Def => New_True_Literal);
                  elsif Entity (Expr) = Standard_False then
                     T := New_Prog_Constant (Def => New_False_Literal);
                  else
                     T := New_Prog_Identifier
                           (Ada_Node => Expr,
                            Def      => Why_Ident_Of_Ada_Ident (Expr));
                  end if;

               when others =>
                  --  There is a special case for constants introduced by the
                  --  frontend
                  if Ekind (Entity (Expr)) = E_Constant and then not
                     (Comes_From_Source (Original_Node (Entity (Expr)))) then
                     T := New_Prog_Identifier
                           (Ada_Node => Expr,
                            Def      =>
                              New_Identifier
                                 (Symbol => Chars (Entity (Expr))));
                  elsif Is_Mutable (Entity (Expr)) then
                     T := New_Deref
                           (Ada_Node => Expr,
                            Ref      => Why_Ident_Of_Ada_Ident (Expr));
                  else
                     T := New_Prog_Identifier
                           (Ada_Node => Expr,
                            Def      => Why_Ident_Of_Ada_Ident (Expr));
                  end if;
                  if Ekind (Entity (Expr)) = E_Loop_Parameter then
                     Current_Type := (Kind => Why_Int);
                  end if;

            end case;

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

         when N_Op_Add | N_Op_Multiply | N_Op_Subtract  =>
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

         when N_Op_Divide =>
            T :=
               New_Located_Call
                 (Ada_Node => Expr,
                  Name     => To_Program_Space (New_Integer_Division),
                  Progs =>
                     (1 =>
                        Why_Expr_Of_Ada_Expr
                           (Left_Opnd (Expr),
                            (Kind => Why_Int)),
                      2 =>
                        Why_Expr_Of_Ada_Expr
                           (Right_Opnd (Expr),
                            (Kind => Why_Int))));
            Current_Type := (Kind => Why_Int);

         when N_Op_Ge .. N_Op_Ne =>
            return
              New_Infix_Call
                (Ada_Node => Expr,
                 Infix    => Why_Prog_Binop_Of_Ada_Op (Nkind (Expr)),
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
                   Why_Expr_Of_Ada_Expr
                     (First (Expressions (Expr)),
                      (Why_Abstract,
                       Type_Of_Node
                         (First_Index (Etype (Prefix (Expr)))))));

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
      return Why_Expr_Of_Ada_Expr (Expr, (Why_Abstract, Type_Of_Node (Expr)));
   end Why_Expr_Of_Ada_Expr;

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
                            (Expression (Stmt),
                             (Why_Abstract, Type_Of_Node (Lvalue))));

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
                            (Why_Abstract,
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
               return New_Void (Stmt);
            end if;

         when N_Procedure_Call_Statement =>
            --  Ignore calls to procedures generated for postconditions

            if Is_Postcondition_Proc (Entity (Name (Stmt))) then
               return New_Void (Stmt);
            end if;

            declare
               Proc_Name : constant W_Identifier_Id :=
                  New_Identifier (Symbol => Chars (Entity (Name (Stmt))));
               Len       : constant Nat :=
                  List_Length (Parameter_Associations (Stmt));
            begin
               if Len = 0 then
                  return
                     New_Located_Call
                        (Ada_Node => Stmt,
                         Name     => Proc_Name,
                         Progs    => (1 => New_Void (Stmt)));
               else
                  declare
                     Cur_Formal : Node_Id :=
                        First_Entity (Entity (Name (Stmt)));
                     Cur_Actual : Node_Id :=
                        First (Parameter_Associations (Stmt));
                     Why_Args : W_Prog_Array :=
                        (1 .. Integer (Len) => Why.Types.Why_Empty);
                     Cnt      : Positive := 1;
                  begin
                     while Present (Cur_Formal) loop
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
                                 Why_Expr_Of_Ada_Expr (Cur_Actual);
                        end case;
                        Cur_Formal := Next_Entity (Cur_Formal);
                        Next (Cur_Actual);
                        Cnt := Cnt + 1;
                     end loop;
                     return
                        New_Located_Call
                          (Ada_Node => Stmt,
                           Name     => Proc_Name,
                           Progs    => Why_Args);
                  end;
               end if;
            end;

         when N_If_Statement =>
            return
              New_Conditional_Prog
                (Ada_Node  => Stmt,
                 Condition => Why_Expr_Of_Ada_Expr (Condition (Stmt)),
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
            declare
               Loop_Body    : constant List_Id := Statements (Stmt);
               Split_Node   : Node_Id;
               Invariant    : W_Predicate_Id;
               Loop_Content : W_Prog_Id;
               Annot        : W_Loop_Annot_Id;
               Scheme       : constant Node_Id := Iteration_Scheme (Stmt);
            begin
               Compute_Invariant (Loop_Body, Invariant, Split_Node);
               Loop_Content :=
                  Why_Expr_Of_Ada_Stmts
                    (Stmts      => Loop_Body,
                     Start_from => Split_Node);
               Annot :=
                 New_Loop_Annot
                   (Ada_Node  => Stmt,
                    Invariant => New_Assertion (Pred => Invariant));
               if Nkind (Scheme) = N_Empty then
                  --  No iteration scheme, we have a simple loop
                  return
                    New_While_Loop
                      (Ada_Node     => Stmt,
                       Condition    =>
                         New_Prog_Constant (Def => New_True_Literal),
                       Annotation   => Annot,
                       Loop_Content => Loop_Content);
               elsif Nkind (Iterator_Specification (Scheme)) = N_Empty
                  and then
                     Nkind (Loop_Parameter_Specification (Scheme)) = N_Empty
               then
                  --  We are in a While loop
                  return
                    New_While_Loop
                      (Ada_Node     => Stmt,
                       Condition    =>
                         Why_Expr_Of_Ada_Expr (Condition (Scheme)),
                       Annotation   => Annot,
                       Loop_Content => Loop_Content);
               elsif Nkind (Condition (Scheme)) = N_Empty then
                  --  We are in a For loop
                  --  ??? Only increasing loops for now
                  declare
                     LParam_Spec : constant Node_Id :=
                        Loop_Parameter_Specification (Scheme);
                     Low : constant Node_Id :=
                        Low_Bound
                          (Get_Range
                            (Discrete_Subtype_Definition (LParam_Spec)));
                     High : constant Node_Id :=
                        High_Bound
                          (Get_Range
                            (Discrete_Subtype_Definition (LParam_Spec)));
                     Loop_Index : constant Name_Id :=
                        Chars (Defining_Identifier (LParam_Spec));
                  begin
                     return
                        New_For_Loop
                        (Ada_Node  => Stmt,
                        Loop_Index => Loop_Index,
                        Low        =>
                           Why_Expr_Of_Ada_Expr (Low, (Kind => Why_Int)),
                        High       =>
                           Why_Expr_Of_Ada_Expr (High, (Kind => Why_Int)),
                        Invariant  => Annot,
                        Loop_Body  => Loop_Content);
                  end;
               else
                  --  Some other kind of loop
                  raise Not_Implemented;
               end if;
            end;

         when N_Exit_Statement =>
            declare
               Raise_Stmt : constant W_Prog_Id :=
                 New_Raise_Statement
                   (Ada_Node => Stmt,
                    Name => New_Exit_Identifier);
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

         when others =>
            raise Not_Implemented;
      end case;
   end Why_Expr_Of_Ada_Stmt;

   ---------------------------
   -- Why_Expr_Of_Ada_Stmts --
   ---------------------------

   function Why_Expr_Of_Ada_Stmts
     (Stmts      : List_Id;
      Start_from : Node_Id := Empty)
     return W_Prog_Id
   is
      Result          : W_Prog_Id := New_Void;
      Cur_Stmt        : Node_Or_Entity_Id;
      Seen_Statements : Boolean := False;
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
      --  The variable Result contains the already translated part. The
      --  boolean Seen_Statements stores if Result contains something else
      --  than the default value (void)
      if List_Length (Stmts) = 0 then
         --  We return the default value, ie void
         return Result;
      end if;

      Cur_Stmt := Nlists.Last (Stmts);

      while Cur_Stmt /= Start_from and then Nkind (Cur_Stmt) /= N_Empty loop
         case Nkind (Cur_Stmt) is
            when N_Null_Statement =>
               null;

            when N_Object_Declaration =>
               --  Source objects should be defined at a global level

               if Seen_Statements and then
                  not Comes_From_Source (Original_Node (Cur_Stmt))
               then
                  declare
                     Id       : constant Node_Id :=
                        Defining_Identifier (Cur_Stmt);
                     W_Id     : constant W_Identifier_Id :=
                        New_Identifier (Symbol => Chars (Id));
                     Exp_Type : constant Why_Type :=
                        (Why_Abstract,
                         Type_Of_Node (Object_Definition (Cur_Stmt)));
                  begin
                     case Ekind (Id) is
                        when E_Constant =>
                           Result := New_Binding_Prog
                             (Ada_Node => Cur_Stmt,
                              Name     => W_Id,
                              Def      =>
                                Why_Expr_Of_Ada_Expr
                                  (Expression (Cur_Stmt),
                                   Exp_Type),
                              Context  => Result);
                        when others =>
                           Result := New_Binding_Ref
                             (Ada_Node => Cur_Stmt,
                              Name     => W_Id,
                              Def      =>
                                Why_Expr_Of_Ada_Expr
                                  (Expression (Cur_Stmt),
                                   Exp_Type),
                              Context  => Result);
                     end case;
                  end;
               end if;

            when others =>
               --  For all other statements, we call Why_Expr_Of_Ada_Stmt
               --  to obtain a stmt, and if necessary we build a statement
               --  sequence
               if not Seen_Statements then
                  Result := Why_Expr_Of_Ada_Stmt (Cur_Stmt);
                  Seen_Statements := True;
               else
                  Result := Sequence (Why_Expr_Of_Ada_Stmt (Cur_Stmt), Result);
               end if;
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
         when N_Identifier | N_Indexed_Component =>
            return
              New_Related_Terms
                (Ada_Node => Expr,
                 Left     => Why_Term_Of_Ada_Expr (Expr),
                 Right    => New_True_Literal,
                 Op       => New_Rel_Eq);

         when N_Op_Eq |
              N_Op_Ne =>
            --  ??? Select left type as more general type for now
            return
              New_Related_Terms
                (Ada_Node => Expr,
                 Left     => Why_Term_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    =>
                   Why_Term_Of_Ada_Expr (Right_Opnd (Expr),
                    (Why_Abstract, Type_Of_Node (Left_Opnd (Expr)))),
                 Op       => Why_Rel_Of_Ada_Op (Nkind (Expr)));

         when N_Op_Ge |
              N_Op_Gt |
              N_Op_Le |
              N_Op_Lt =>
            --  In Why, the builtin comparison functions expect type "int"
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
              New_Conjunction
                (Ada_Node => Expr,
                 Left     => Why_Predicate_Of_Ada_Expr (Left_Opnd (Expr)),
                 Right    => Why_Predicate_Of_Ada_Expr (Right_Opnd (Expr)));

         when N_Op_Or | N_Or_Else =>
            return
              New_Disjunction
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

         when others =>
            raise Not_Implemented;
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
      Current_Type : Why_Type := (Why_Abstract, Type_Of_Node (Expr));
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
                 Name     => Why_Ident_Of_Ada_Ident (Expr));

         when N_Op_Add | N_Op_Multiply | N_Op_Subtract =>
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
         when N_Op_Divide =>
            T :=
               New_Operation
                 (Ada_Node   => Expr,
                  Name       => New_Integer_Division,
                  Parameters =>
                    (1 =>
                       Why_Term_Of_Ada_Expr
                         (Left_Opnd (Expr),
                           (Kind => Why_Int)),
                     2 =>
                       Why_Term_Of_Ada_Expr
                         (Right_Opnd (Expr),
                          (Kind => Why_Int))));
            Current_Type := (Kind =>  Why_Int);
         when N_Op_Compare =>
            return
               New_Operation
                 (Ada_Node => Expr,
                  Name =>
                    New_Bool_Int_Cmp
                      (Get_Kind (Why_Rel_Of_Ada_Op (Nkind (Expr)))),
                  Parameters =>
                     (1 =>
                        Why_Term_Of_Ada_Expr
                          (Left_Opnd (Expr), (Kind => Why_Int)),
                      2 =>
                        Why_Term_Of_Ada_Expr
                          (Right_Opnd (Expr), (Kind => Why_Int))));

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
                     (Why_Abstract,
                      Type_Of_Node (First_Index (Etype (Prefix (Expr))))))
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
               elsif Attr_Name = Name_Last then
                  --  ??? Not sure about this
                  T :=
                     New_Integer_Constant
                        (Ada_Node => Expr,
                         Value =>
                           Expr_Value
                              (High_Bound (First_Index (Etype (Var)))));
               else
                  raise Not_Implemented;
               end if;
            end;

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
      return Why_Term_Of_Ada_Expr (Expr, (Why_Abstract, Type_Of_Node (Expr)));
   end Why_Term_Of_Ada_Expr;

end Gnat2Why.Subprograms;
