------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - E X P R                         --
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

with Einfo;              use Einfo;
with Namet;              use Namet;
with Nlists;             use Nlists;
with Snames;             use Snames;
with Stand;              use Stand;
with String_Utils;       use String_Utils;
with Uintp;              use Uintp;
with VC_Kinds;           use VC_Kinds;

with Why;                   use Why;
with Why.Types;             use Why.Types;
with Why.Inter;             use Why.Inter;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Accessors;   use Why.Atree.Accessors;
with Why.Gen.Arrays;        use Why.Gen.Arrays;
with Why.Gen.Expr;          use Why.Gen.Expr;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Progs;         use Why.Gen.Progs;
with Why.Gen.Terms;         use Why.Gen.Terms;
with Why.Conversions;       use Why.Conversions;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Expr.Loops;   use Gnat2Why.Expr.Loops;
with Gnat2Why.Subprograms;  use Gnat2Why.Subprograms;
with Gnat2Why.Types;        use Gnat2Why.Types;

package body Gnat2Why.Expr is

   function Case_Expr_Of_Ada_Node (N : Node_Id; Domain : EW_Domain)
      return W_Expr_Id;
   --  Build Case expression of Ada Node.

   function Compute_Call_Args (Call : Node_Id; Domain : EW_Domain)
      return W_Expr_Array;
   --  Compute arguments for a function call or procedure call. The node in
   --  argument must have a "Name" field and a "Parameter_Associations" field.

   function Equal_To (E : W_Expr_Id; N : Node_Id; Domain : EW_Domain)
      return W_Expr_Id;
   --  For an expression E of type "int" and a Node that represents a
   --  Discrete_Choice, build an expression that expresses that T belongs to
   --  the range expressed by N.

   procedure Extract_From_Quantified_Expression
      (N       : Node_Id;
       Index   : out W_Identifier_Id;
       Range_E : out Node_Id);
   --  Extract the loop index and the range expression node from a
   --  QUANTIFIED_EXPRESSION

   generic
      with procedure Handle_Argument (Formal, Actual : Node_Id);
   procedure Iterate_Call_Arguments (Call : Node_Id);
   --  Call "Handle_Argument" for each pair Formal/Actual of a function or
   --  procedure call. The node in argument must have a "Name" field and a
   --  "Parameter_Associations" field.

   function One_Level_Access
      (N      : Node_Id;
       Expr   : W_Expr_Id;
       Domain : EW_Domain)
      return W_Expr_Id;
   --  Compute an access expression for record and array accesses without
   --  considering subexpressions. [N] represents the Ada node of the access,
   --  and [Expr] the Why expression of the prefix.

   function One_Level_Update
      (N      : Node_Id;
       Pref   : W_Expr_Id;
       Value  : W_Expr_Id;
       Domain : EW_Domain)
      return W_Expr_Id;
   --  same as One_Level_Access, but for updates

   function Transform_Quantified_Expression
      (Expr         : Node_Id;
       Domain       : EW_Domain;
       Current_Type : out W_Base_Type_Id) return W_Expr_Id;

   function Transform_Statement (Stmt : Node_Id) return W_Prog_Id;

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id;
   --  Translate a single Ada statement into a Why expression

   function Transform_Array_Component_Associations
     (Typ    : Entity_Id;
      Id     : W_Identifier_Id;
      Exprs  : List_Id;
      Assocs : List_Id) return W_Pred_Id;

   function Transform_Record_Component_Associations
     (Domain : EW_Domain;
      Typ    : Entity_Id;
      Assocs : List_Id)
     return W_Field_Association_Array;

   function Transform_Binop (Op : N_Binary_Op) return EW_Binary_Op;
   --  Convert an Ada binary operator to a Why term symbol

   function Transform_Enum_Literal
     (Enum         : Node_Id;
      Current_Type : out W_Base_Type_Id;
      Domain       : EW_Domain)
      return W_Expr_Id;
   --  Translate an Ada enumeration literal to Why. There are a number of
   --  special cases, so its own function is appropriate.

   function Transform_Compare_Op (Op : N_Op_Compare) return EW_Relation;
   --  Convert an Ada comparison operator to a Why relation symbol

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
                         +Transform_Expr (Rexpr,
                                          Type_Of_Node (Lvalue),
                                          EW_Prog);
            L_Name   : constant String := Full_Name (Lvalue);
            L_Id     : constant W_Identifier_Id := New_Identifier (L_Name);
         begin
            if Is_Mutable (Lvalue) then
               return New_Assignment
                 (Ada_Node => N,
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
                  Eq      : constant W_Pred_Id :=
                              New_Relation
                                (Op      => EW_Eq,
                                 Op_Type => Get_EW_Type (Lvalue),
                                 Left    => +Tmp_Var,
                                 Right   => +L_Id);
               begin
                  return
                    New_Binding
                      (Ada_Node => N,
                       Name     => Tmp_Var,
                       Def      => +Why_Expr,
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

   function Case_Expr_Of_Ada_Node (N : Node_Id; Domain : EW_Domain)
      return W_Expr_Id
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

      function Branch_Expr (N : Node_Id) return W_Expr_Id;
      --  Return the expression that corresponds to a branch; decide which
      --  function to call depending on the type of the branch.

      function Branch_Expr (N : Node_Id) return W_Expr_Id
      is
      begin
         case Nkind (N) is
            when N_Case_Expression_Alternative =>
               return Transform_Expr (Expression (N), Domain);

            when N_Case_Statement_Alternative =>
               --  ??? Maybe we should merge the code for statements?
               return +Transform_Statements (Statements (N));

            when others =>
               raise Unexpected_Node;

         end  case;
      end Branch_Expr;

      Match_Domain  : constant EW_Domain :=
         (if Domain = EW_Pred then EW_Term else Domain);
      Cond_Domain  : constant EW_Domain :=
         (if Domain = EW_Term then EW_Pred else Domain);

      Cur_Case     : Node_Id := Last (Alternatives (N));
      Matched_Expr : constant W_Expr_Id :=
                       Transform_Expr (Expression (N),
                                       EW_Int_Type,
                                       Match_Domain);

      --  We always take the last branch as the default value
      T            : W_Expr_Id := Branch_Expr (Cur_Case);

      --  beginning of processing for Case_Expr_Of_Ada_Node
   begin
      Cur_Case := Prev (Cur_Case);
      while Present (Cur_Case) loop
         declare
            Cur_Choice : Node_Id := First (Discrete_Choices (Cur_Case));
            C          : W_Expr_Id :=
                           New_Literal
                             (Domain => Cond_Domain,
                              Value  => EW_False);
         begin
            while Present (Cur_Choice) loop
               C := New_Or_Else_Expr
                      (C,
                       Equal_To (Matched_Expr, Cur_Choice, Cond_Domain),
                       Cond_Domain);
               Next (Cur_Choice);
            end loop;

            declare
               Then_Part : W_Expr_Id;
            begin
               case Nkind (Cur_Case) is
                  when N_Case_Expression_Alternative =>
                     Then_Part :=
                        Transform_Expr (Expression (Cur_Case), Domain);

                  when N_Case_Statement_Alternative =>
                     Then_Part :=
                        +Transform_Statements (Statements (Cur_Case));

                  when others =>
                     raise Unexpected_Node;

               end  case;
               T :=
                  New_Simpl_Conditional
                     (Condition => C,
                      Then_Part => Then_Part,
                      Else_Part => T,
                      Domain    => Domain);
            end;
         end;
         Prev (Cur_Case);
      end loop;
      return T;
   end Case_Expr_Of_Ada_Node;

   -----------------------
   -- Compute_Call_Args --
   -----------------------

   function Compute_Call_Args (Call : Node_Id; Domain : EW_Domain)
      return W_Expr_Array
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
                  Why_Args (Cnt) := +Transform_Ident (Actual);

               when others =>
                  --  No special treatment for parameters that are
                  --  not "out"
                  Why_Args (Cnt) :=
                    Transform_Expr (Actual,
                                    Type_Of_Node (Formal),
                                    Domain);
            end case;
            Cnt := Cnt + 1;
         end Compute_Arg;

         procedure Iterate_Call is new
           Iterate_Call_Arguments (Compute_Arg);
      begin
         Iterate_Call (Call);
         return Why_Args;
      end;
   end Compute_Call_Args;

   --------------
   -- Equal_To --
   --------------

   function Equal_To
     (E      : W_Expr_Id;
      N      : Node_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
         (if Domain = EW_Pred then EW_Term else Domain);
   begin
      case Nkind (N) is
         when N_Identifier
           | N_Real_Literal
           | N_Integer_Literal =>
            declare
               BT : constant W_Base_Type_Id := Base_Why_Type (N);
            begin
               return
                 New_Comparison
                 (Cmp       => EW_Eq,
                  Left      => E,
                  Right     => Transform_Expr (N, BT, Subdomain),
                  Arg_Types => BT,
                  Domain    => Domain);
            end;

         when N_Range =>
            return
              New_And_Expr
                (Left  =>
                   New_Comparison
                     (Cmp       => EW_Le,
                      Left      => Transform_Expr (Low_Bound (N),
                                                   EW_Int_Type,
                                                   Subdomain),
                      Arg_Types => New_Base_Type (Base_Type => EW_Int),
                      Right     => E,
                      Domain    => Domain),
                 Right =>
                   New_Comparison
                     (Cmp       => EW_Le,
                      Left      => E,
                      Right     => Transform_Expr (High_Bound (N),
                                                   EW_Int_Type,
                                                   Subdomain),
                      Arg_Types => New_Base_Type (Base_Type => EW_Int),
                      Domain    => Domain),
                 Domain => Domain);

         when N_Others_Choice =>
            return New_Literal (Domain => Domain, Value => EW_True);

         when others =>
            raise Not_Implemented;

      end case;
   end Equal_To;

   ----------------------------------------
   -- Extract_From_Quantified_Expression --
   ----------------------------------------

   procedure Extract_From_Quantified_Expression
      (N       : Node_Id;
       Index   : out W_Identifier_Id;
       Range_E : out Node_Id)
   is
      Spec : Node_Id;
   begin
      if Present (Loop_Parameter_Specification (N)) then
         Spec := Loop_Parameter_Specification (N);
         Range_E := Discrete_Subtype_Definition (Spec);

      elsif Present (Iterator_Specification (N)) then
         Spec := Iterator_Specification (N);
         Range_E := Name (Spec);

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
           | N_Modular_Type_Definition
           | N_Floating_Point_Definition
           | N_Ordinary_Fixed_Point_Definition
           | N_Decimal_Fixed_Point_Definition =>
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

   ----------------------
   -- One_Level_Access --
   ----------------------

   function One_Level_Access
      (N      : Node_Id;
       Expr   : W_Expr_Id;
       Domain : EW_Domain)
      return W_Expr_Id
   is
   begin
      case Nkind (N) is
         when N_Selected_Component =>
            return
               New_Record_Access
                 (Name   => Expr,
                  Field  => Transform_Ident (Selector_Name (N)));

         when N_Indexed_Component =>
            --  ??? Save the index in a temporary variable
            declare
               Cnt      : Integer := 1;
               Ar     : constant Node_Id := Prefix (N);
               Index  : Node_Id := First (Expressions (N));
               T_Name : constant String := Type_Of_Node (Ar);
               T      : W_Expr_Id := Expr;
            begin
               while Present (Index) loop
                  T :=
                    New_Array_Access
                     (Ada_Node => N,
                      Domain   => Domain,
                      Type_Name =>
                        (if Cnt = 1 then T_Name
                         else T_Name & "___" & Int_Image (Cnt)),
                      Ar        => T,
                      Index     =>
                        Transform_Expr (Index, EW_Int_Type, Domain));
                  Next (Index);
                  Cnt := Cnt + 1;
               end loop;
               return T;
            end;

         when others =>
            raise Not_Implemented;

      end case;
   end One_Level_Access;

   ----------------------
   -- One_Level_Update --
   ----------------------

   function One_Level_Update
      (N      : Node_Id;
       Pref   : W_Expr_Id;
       Value  : W_Expr_Id;
       Domain : EW_Domain)
      return W_Expr_Id is
   begin
      case Nkind (N) is
         when N_Selected_Component =>
            return
              New_Record_Update (Name  => Pref,
                                 Field => Transform_Ident (Selector_Name (N)),
                                 Value => Value);

         when N_Indexed_Component =>
            if Number_Dimensions (Etype (Prefix (N))) > 1 then
               raise Not_Implemented;
            end if;
            return
               New_Array_Update (Ada_Node  => N,
                                 Type_Name => Type_Of_Node (Prefix (N)),
                                 Ar        => Pref,
                                 Index     =>
                                    +Transform_Expr
                                      (First (Expressions (N)),
                                       EW_Int_Type,
                                       EW_Prog),
                                 Value     => Value,
                                 Domain    => Domain);

         when others =>
            raise Not_Implemented;

      end case;

   end One_Level_Update;

   ----------------
   -- Range_Expr --
   ----------------

   function Range_Expr (N : Node_Id; T : W_Expr_Id; Domain : EW_Domain)
      return W_Expr_Id
   is
      Subdomain  : constant EW_Domain :=
                     (if Domain = EW_Pred then EW_Term else Domain);
      Range_Node : constant Node_Id := Get_Range (N);
   begin
      return
        New_And_Then_Expr
          (Left  =>
             New_Relation
               (Domain  => Domain,
                Op_Type => EW_Int,
                Op      => EW_Le,
                Left    => +Transform_Expr (Low_Bound (Range_Node),
                                            EW_Int_Type,
                                            Subdomain),
                Right   => +T),
           Right  =>
             New_Relation
               (Domain  => Domain,
                Op_Type => EW_Int,
                Op      => EW_Le,
                Left    => +T,
                Right   => +Transform_Expr (High_Bound (Range_Node),
                                            EW_Int_Type,
                                            Subdomain)),
           Domain => Domain);
   end Range_Expr;

   ------------------------------------
   -- Transform_Assignment_Statement --
   ------------------------------------

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id
   is

      --  Here, we deal with assignment statements. In Alfa, the general form
      --  of an assignment is
      --
      --    Lvalue := Expr;
      --
      --  where Lvalue is a mix of array and record accesses. If we adopt the
      --  same notation for both, we obtain the general form
      --
      --    Prefix.Acc1.Acc2.(...).Accn := Expr;
      --
      --  where the Acc(i) are either array accesses using an index (or
      --  several indices in the multidimensional case) or record accesses
      --  using a field name.
      --
      --  Here, we generate Why code of the form
      --
      --    Prefix := Upd (Prefix, Acc1,
      --                   (Upd (Prefix.Acc1, Acc2,
      --                         Upd (..., Accn, Expr))));

      function Compute_Rvalue (N : Node_Id; Update_Expr : W_Prog_Id)
         return W_Prog_Id;

      function Expected_Type return W_Base_Type_Id;
      --  Compute the expected type of the right hand side expression.

      function Why_Lvalue (N : Node_Id) return W_Identifier_Id;
      --  Compute the innermost that is accessed in the Lvalue, variable, ie
      --  the outermost data structure; this basically corresponds to "Prefix"
      --  above.

      Lvalue   : constant Node_Id := Name (Stmt);
      --  The Lvalue in the Ada sense, ie the chain of accesses

      --------------------
      -- Compute_Rvalue --
      --------------------

      function Compute_Rvalue (N : Node_Id; Update_Expr : W_Prog_Id)
         return W_Prog_Id is

         --  The outermost Access node corresponds to the innermost data
         --  structure; therefore, we compute the update expression before the
         --  recursive call; It happens that the prefix of the current
         --  node precisely corresponds to the data structure to be
         --  updated.
      begin
         case Nkind (N) is
            when N_Identifier | N_Expanded_Name =>

               return Update_Expr;

            when N_Selected_Component | N_Indexed_Component =>
               return
                  Compute_Rvalue
                    (Prefix (N),
                     +One_Level_Update
                       (N,
                        +Transform_Expr (Prefix (N), EW_Prog),
                        +Update_Expr,
                        EW_Prog));

            when others =>
               raise Not_Implemented;

         end case;
      end Compute_Rvalue;

      --------------------
      -- Expected_Type --
      --------------------

      function Expected_Type return W_Base_Type_Id
      is
         --  We simply traverse the Lvalue until we find the innermost access;
         --  the type of the array, or the type of the record field, is the
         --  expected type.
      begin
         case Nkind (Lvalue) is
            when N_Identifier | N_Expanded_Name =>
               return Type_Of_Node (Lvalue);

            when N_Indexed_Component =>
               return Type_Of_Node (Component_Type (Etype (Prefix (Lvalue))));

            when N_Selected_Component =>
               return Type_Of_Node (Selector_Name (Lvalue));

            when others =>
               raise Not_Implemented;

         end case;
      end Expected_Type;

      ----------------
      -- Why_Lvalue --
      ----------------

      function Why_Lvalue (N : Node_Id) return W_Identifier_Id
      is
      begin
         case Nkind (N) is
            when N_Identifier | N_Expanded_Name =>
               return Transform_Ident (N);

            when N_Indexed_Component | N_Selected_Component =>
               return Why_Lvalue (Prefix (N));

            when others =>
               raise Not_Implemented;

         end case;

      end Why_Lvalue;

      --  begin processing for Transform_Assignment_Statement

      W_Lvalue : constant W_Identifier_Id := Why_Lvalue (Lvalue);
   begin
      return
         New_Assignment
            (Ada_Node => Stmt,
             Name     => W_Lvalue,
             Value    =>
               Compute_Rvalue (Lvalue,
                               +Transform_Expr (Expression (Stmt),
                                                Expected_Type,
                                                EW_Prog)));
   end Transform_Assignment_Statement;

   ---------------------
   -- Transform_Binop --
   ---------------------

   function Transform_Binop (Op : N_Binary_Op) return EW_Binary_Op is
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
   end Transform_Binop;

   --------------------------
   -- Transform_Compare_Op --
   --------------------------

   function Transform_Compare_Op (Op : N_Op_Compare) return EW_Relation is
   begin
      case Op is
         when N_Op_Gt => return EW_Gt;
         when N_Op_Lt => return EW_Lt;
         when N_Op_Eq => return EW_Eq;
         when N_Op_Ge => return EW_Ge;
         when N_Op_Le => return EW_Le;
         when N_Op_Ne => return EW_Ne;
      end case;
   end Transform_Compare_Op;

   --------------------------------------------
   -- Transform_Array_Component_Associations --
   --------------------------------------------

   function Transform_Array_Component_Associations
     (Typ    : Entity_Id;
      Id     : W_Identifier_Id;
      Exprs  : List_Id;
      Assocs : List_Id) return W_Pred_Id
   is
      T_Name    : constant String := Type_Of_Node (Typ);
      Index     : constant W_Identifier_Id := New_Temp_Identifier;

      -----------------------
      -- Local subprograms --
      -----------------------

      function Constrain_Value_At_Index
        (Expr_Or_Association : Node_Id) return W_Expr_Id;
      --  Return the proposition that Id (Index) is equal to the value given in
      --  Expr_Or_Association, or else "true" for box association.

      function Select_Nth_Index (Offset : Nat) return W_Expr_Id;
      --  Return the proposition that Index is at Offset from Id'First

      function Select_These_Choices (L : List_Id) return W_Expr_Id;
      --  Return a proposition that expresses that Index satisfies one choice
      --  in the list of choices L.

      function Select_This_Choice (N : Node_Id) return W_Expr_Id;
      --  Return a proposition that expresses that Index satisfies choice N

      ------------------------------
      -- Constrain_Value_At_Index --
      ------------------------------

      function Constrain_Value_At_Index
        (Expr_Or_Association : Node_Id) return W_Expr_Id
      is
      begin
         if Nkind (Expr_Or_Association) = N_Component_Association
           and then Box_Present (Expr_Or_Association)
         then
            return New_Literal (Value  => EW_True,
                                Domain => EW_Pred);
         else
            declare
               Expr      : constant Node_Id :=
                             (if Nkind (Expr_Or_Association) =
                                N_Component_Association
                              then
                                Expression (Expr_Or_Association)
                              else
                                Expr_Or_Association);
               Exp_Type  : constant Node_Id :=
                             (if Number_Dimensions (Typ) = 1 then
                                Component_Type (Typ)
                              else Etype (Expr));
               Elmt_Type : constant W_Base_Type_Id :=
                             +Why_Logic_Type_Of_Ada_Type (Exp_Type);
               Value     : constant W_Expr_Id :=
                             Transform_Expr (Expr          => Expr,
                                             Expected_Type => Elmt_Type,
                                             Domain        => EW_Term);
               Read      : constant W_Expr_Id :=
                             New_Array_Access
                               (Ada_Node  => Expr_Or_Association,
                                Domain    => EW_Term,
                                Type_Name => T_Name,
                                Ar        => +Id,
                                Index     => +Index);
            begin
               return New_Comparison
                 (Cmp       => EW_Eq,
                  Left      => Read,
                  Right     => Value,
                  Arg_Types => Elmt_Type,
                  Domain    => EW_Pred);
            end;
         end if;
      end Constrain_Value_At_Index;

      ----------------------
      -- Select_Nth_Index --
      ----------------------

      function Select_Nth_Index (Offset : Nat) return W_Expr_Id is
         First : constant W_Expr_Id :=
                   New_Array_Attr
                     (Attribute_Id'Image (Attribute_First),
                      T_Name,
                      +Id,
                      EW_Term);
         Nth   : constant W_Expr_Id :=
                   New_Binary_Op
                     (Left     => First,
                      Right    =>
                        New_Integer_Constant (Value  => UI_From_Int (Offset)),
                      Op       => EW_Add,
                      Op_Type  => EW_Int);
      begin
         return New_Comparison
           (Cmp       => EW_Eq,
            Left      => +Index,
            Right     => Nth,
            Arg_Types => EW_Int_Type,
            Domain    => EW_Pred);
      end Select_Nth_Index;

      --------------------------
      -- Select_These_Choices --
      --------------------------

      function Select_These_Choices (L : List_Id) return W_Expr_Id is
         Result : W_Expr_Id := New_Literal (Value  => EW_False,
                                            Domain => EW_Pred);
         Choice : Node_Id   := First (L);
      begin
         while Present (Choice) loop
            Result := New_Or_Expr (Left   => Result,
                                   Right  => Select_This_Choice (Choice),
                                   Domain => EW_Pred);
            Next (Choice);
         end loop;
         return Result;
      end Select_These_Choices;

      ------------------------
      -- Select_This_Choice --
      ------------------------

      function Select_This_Choice (N : Node_Id) return W_Expr_Id is
         In_Range : W_Expr_Id;
      begin
         case Nkind (N) is
            when N_Subtype_Indication | N_Range =>
               In_Range := Range_Expr (N, +Index, EW_Pred);
               return In_Range;
            when N_Others_Choice =>
               raise Program_Error;
            when others =>
               In_Range :=
                 New_Comparison
                   (Cmp       => EW_Eq,
                    Left      => +Index,
                    Right     => Transform_Expr (Expr          => N,
                                                 Expected_Type => EW_Int_Type,
                                                 Domain        => EW_Term),
                    Arg_Types => EW_Int_Type,
                    Domain    => EW_Pred);
               return In_Range;
         end case;
      end Select_This_Choice;

      Association : Node_Id;
      Expression  : Node_Id;
      Offset      : Nat;
      Completion  : W_Expr_Id := New_Literal (Value  => EW_True,
                                              Domain => EW_Pred);

   begin
      Association :=
        (if Nlists.Is_Empty_List (Assocs) then Empty
         else Nlists.Last (Assocs));

      --  Special case for "others" choice, which must appear alone as last
      --  association.

      if Present (Association)
        and then List_Length (Choices (Association)) = 1
        and then Nkind (First (Choices (Association))) = N_Others_Choice
      then
         if not Box_Present (Association) then
            Completion := Constrain_Value_At_Index (Association);
         end if;
         Prev (Association);
      end if;

      Expression :=
        (if Nlists.Is_Empty_List (Exprs) then Empty else Nlists.Last (Exprs));
      Offset     := List_Length (Exprs);
      if Present (Expression) then
         pragma Assert (No (Association));
         while Present (Expression) loop
            Offset := Offset - 1;
            Completion := New_Conditional
              (Domain    => EW_Pred,
               Condition => +Select_Nth_Index (Offset),
               Then_Part => Constrain_Value_At_Index (Expression),
               Else_Part => Completion);
            Prev (Expression);
         end loop;

      else
         while Present (Association) loop
            Completion := New_Conditional
              (Domain    => EW_Pred,
               Condition => +Select_These_Choices (Choices (Association)),
               Then_Part => Constrain_Value_At_Index (Association),
               Else_Part => Completion);
            Prev (Association);
         end loop;
      end if;

      return New_Universal_Quantif
        (Variables => (1 => Index),
         Var_Type  => +EW_Int_Type,
         Pred      => +Completion);
   end Transform_Array_Component_Associations;

   ---------------------------------------------
   -- Transform_Record_Component_Associations --
   ---------------------------------------------

   function Transform_Record_Component_Associations
     (Domain : EW_Domain;
      Typ    : Entity_Id;
      Assocs : List_Id)
     return W_Field_Association_Array
   is
      function Matching_Component_Association
        (Component   : Entity_Id;
         Association : Node_Id) return Boolean;
      --  Return whether Association matches Component

      function Number_Components (Typ : Entity_Id) return Natural;
      --  Count the number of components in record type Typ

      ------------------------------------
      -- Matching_Component_Association --
      ------------------------------------

      function Matching_Component_Association
        (Component   : Entity_Id;
         Association : Node_Id) return Boolean
      is
         CL : constant List_Id := Choices (Association);
      begin
         pragma Assert (List_Length (CL) = 1);
         return Component = Entity (First (CL));
      end Matching_Component_Association;

      -----------------------
      -- Number_Components --
      -----------------------

      function Number_Components (Typ : Entity_Id) return Natural is
         Count     : Natural := 0;
         Component : Entity_Id := First_Component (Typ);
      begin
         while Component /= Empty loop
            Count := Count + 1;
            Component := Next_Component (Component);
         end loop;
         return Count;
      end Number_Components;

      Component   : Entity_Id := First_Component (Typ);
      Association : Node_Id := Nlists.First (Assocs);
      Result      : W_Field_Association_Array (1 .. Number_Components (Typ));
      J           : Positive := Result'First;

   --  Start of Transform_Record_Component_Associations

   begin
      while Component /= Empty loop
         declare
            Expr : W_Expr_Id;
         begin
            if Present (Association)
              and then Matching_Component_Association (Component, Association)
            then
               if not Box_Present (Association) then
                  Expr := Transform_Expr (Expression (Association), Domain);
               else
                  Expr :=
                     New_Simpl_Any_Expr
                         (Domain => Domain,
                          Arg_Type =>
                            +Why_Logic_Type_Of_Ada_Type (Etype (Component)));
               end if;
               Next (Association);
            else
               Expr :=
                 New_Simpl_Any_Expr
                   (Domain => Domain,
                    Arg_Type =>
                      +Why_Logic_Type_Of_Ada_Type (Etype (Component)));
            end if;
            Result (J) :=
               New_Field_Association
                  (Domain => Domain,
                   Field  => New_Identifier (Full_Name (Component)),
                   Value  => Expr);
            J := J + 1;
            Component := Next_Component (Component);
         end;
      end loop;
      pragma Assert (No (Association));
      return Result;
   end Transform_Record_Component_Associations;

   ----------------------------
   -- Transform_Enum_Literal --
   ----------------------------

   function Transform_Enum_Literal
     (Enum         : Node_Id;
      Current_Type : out W_Base_Type_Id;
      Domain       : EW_Domain)
      return W_Expr_Id is
   begin
      --  Deal with special cases: True/False for boolean values

      if Entity (Enum) = Standard_True then
         Current_Type := Why_Types (EW_Bool);
         return New_Literal (Value => EW_True, Domain => Domain);
      end if;

      if Entity (Enum) = Standard_False then
         Current_Type := Why_Types (EW_Bool);
         return New_Literal (Value => EW_False, Domain => Domain);
      end if;

      --  In the case of a subtype of an enumeration, we need to insert a
      --  conversion. We do so here by modifying the Current_Type; the
      --  conversion itself will be inserted by Transform_Expr.

      Current_Type := EW_Abstract (Etype (Entity (Enum)));
      return +Transform_Ident (Enum);
   end Transform_Enum_Literal;

   --------------------
   -- Transform_Expr --
   --------------------

   function Transform_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id;
      Domain        : EW_Domain) return W_Expr_Id
   is
      T                     : W_Expr_Id;
      Current_Type          : W_Base_Type_Id := Type_Of_Node (Expr);
      Overflow_Check_Needed : Boolean := False;
   begin

      --  Expressions that cannot be translated to predicates directly are
      --  translated to (boolean) terms, and compared to "True"

      if Domain = EW_Pred and then
         not (Nkind (Expr) in N_Op_Compare | N_Op_Not | N_Op_And | N_And_Then
         | N_Op_Or | N_Or_Else | N_In | N_Conditional_Expression |
         N_Quantified_Expression | N_Case_Expression) and then
         not (Nkind (Expr) in N_Identifier | N_Expanded_Name and then
              Ekind (Entity (Expr)) in E_Enumeration_Literal and then
              (Entity (Expr) = Standard_True or else
               Entity (Expr) = Standard_False))
      then
         return
           New_Relation
             (Ada_Node => Expr,
              Domain   => EW_Pred,
              Op_Type  => EW_Bool,
              Left     => +Transform_Expr (Expr, EW_Bool_Type, EW_Term),
              Right    => New_Literal (Value => EW_True, Domain => EW_Prog),
              Op       => EW_Eq);
      end if;

      case Nkind (Expr) is
         when N_Aggregate =>
            if Is_Record_Type (Etype (Expr)) then
               pragma Assert (No (Expressions (Expr)));
               T :=
                  New_Record_Aggregate
                    (Associations => Transform_Record_Component_Associations
                                       (Domain,
                                        Etype (Expr),
                                        Component_Associations (Expr)));
               Current_Type := EW_Abstract (Etype (Expr));
            else
               declare
                  Id : constant W_Identifier_Id :=
                         (if Domain = EW_Term then
                            New_Temp_Identifier
                          else New_Result_Identifier.Id);
                  Base_Type : constant Entity_Id := Etype (Expr);
                  BT : constant W_Base_Type_Id :=
                                +Why_Logic_Type_Of_Ada_Type (Base_Type);
               begin
                  T := New_Simpl_Any_Expr
                    (Domain   => Domain,
                     Arg_Type => +BT,
                     Id       => Id,
                     Pred     =>
                       Transform_Array_Component_Associations
                         (Base_Type,
                          Id,
                          Expressions (Expr),
                          Component_Associations (Expr)));
                  Current_Type := EW_Abstract (Base_Type);
               end;
            end if;

         when N_Integer_Literal =>
            T :=
              New_Integer_Constant
                (Ada_Node => Expr,
                 Value    => Intval (Expr));
            Current_Type := EW_Int_Type;

         when N_Real_Literal =>
            --  The original is usually much easier to process for alt-ergo
            --  than the rewritten node; typically, the will be in decimal
            --  base whereas the expanded node will be of the form
            --  (Num / (2 ** Den)). The division is a problem for alt-ergo,
            --  even between two litterals.

            if Is_Rewrite_Substitution (Expr) then
               begin
                  T := Transform_Expr (Original_Node (Expr),
                                       EW_Real_Type,
                                       Domain);

               --  It may happen that the original node is not in
               --  alfa, whereas the rewritten one is: typically,
               --  if the original node uses exponentiation. So try
               --  the original node and fall back to the rewritten
               --  node if failed.

               exception
                  when Not_Implemented =>
                     T :=
                       New_Real_Constant
                         (Ada_Node => Expr,
                          Value    => Realval (Expr));
               end;

            else
               T :=
                 New_Real_Constant
                   (Ada_Node => Expr,
                    Value    => Realval (Expr));
            end if;

            Current_Type := EW_Real_Type;

         when N_Character_Literal =>

            T :=
              New_Integer_Constant (Ada_Node => Expr,
                                    Value    => Char_Literal_Value (Expr));
            Current_Type := EW_Int_Type;

         --  Deal with identifiers:
         --  * Enumeration literals: deal with special cases True and
         --    False, otherwise such literals are just constants
         --  * local variables are always references
         --  * global constants are logics in Why
         --  * global mutable variables are references
         --  * loop parameters are always mutable, and of type int

         when N_Identifier | N_Expanded_Name =>
            declare
               Id : constant W_Identifier_Id := Transform_Ident (Expr);
            begin
               case Ekind (Entity (Expr)) is
                  --  First treat special cases

                  when E_Enumeration_Literal =>
                     T := Transform_Enum_Literal (Expr, Current_Type, Domain);

                  when others =>
                     if Is_Mutable (Entity (Expr)) then
                        T :=
                          New_Unary_Op
                            (Ada_Node => Expr,
                             Domain   => Domain,
                             Op       => EW_Deref,
                             Right    => +Id,
                             Op_Type  => EW_Int);
                     else
                        T := +Id;
                     end if;

                     if Ekind (Entity (Expr)) = E_Loop_Parameter then
                        Current_Type := EW_Int_Type;
                     end if;

               end case;
            end;

         when N_Op_Compare =>
            declare
               Left      : constant Node_Id := Left_Opnd (Expr);
               Right     : constant Node_Id := Right_Opnd (Expr);
               BT        : constant W_Base_Type_Id :=
                             Base_Why_Type (Left, Right);
               Subdomain : constant EW_Domain :=
                             (if Domain = EW_Pred then EW_Term else Domain);
               Left_Arg  : constant W_Expr_Id :=
                             Transform_Expr (Left, BT, Subdomain);
               Right_Arg : constant W_Expr_Id :=
                             Transform_Expr (Right, BT, Subdomain);
            begin
               if Is_Array_Type (Etype (Left)) then
                  T := New_Call (Ada_Node => Expr,
                                 Domain   => Subdomain,
                                 Name     => Array_Equal_Name.Id (Ada_Array),
                                 Args     =>
                                   (1 => Left_Arg,
                                    2 => Right_Arg));
                  if Domain = EW_Pred then
                     T := New_Comparison
                       (Cmp       => Transform_Compare_Op (Nkind (Expr)),
                        Left      => T,
                        Right     => New_Literal (Domain => Subdomain,
                                                  Value  => EW_True),
                        Arg_Types => EW_Bool_Type,
                        Domain    => Domain);
                  end if;
               else
                  T := New_Comparison
                    (Cmp       => Transform_Compare_Op (Nkind (Expr)),
                     Left      => Left_Arg,
                     Right     => Right_Arg,
                     Arg_Types => BT,
                     Domain    => Domain);
               end if;
               Current_Type := EW_Bool_Type;
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
                    Domain   => Domain,
                    Op       => EW_Minus,
                    Right    =>
                      +Transform_Expr (Right, Current_Type, Domain),
                    Op_Type  => Get_Base_Type (Current_Type));
               Overflow_Check_Needed := True;
            end;

         when N_Op_Abs =>
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Right);
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => New_Abs (Get_Base_Type (Current_Type)),
                    Args    =>
                       (1 => Transform_Expr (Right, Current_Type, Domain)));
               Overflow_Check_Needed := True;
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
                    Left     => Transform_Expr (Left,
                                                Current_Type,
                                                Domain),
                    Right    => Transform_Expr (Right,
                                                Current_Type,
                                                Domain),
                    Op       => Transform_Binop (Nkind (Expr)),
                    Op_Type  => Get_Base_Type (Current_Type));
               Overflow_Check_Needed := True;
            end;

         when N_Op_Divide =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Name  : W_Identifier_Id;
            begin
               Current_Type := Base_Why_Type (Left, Right);
               --  ??? What about Float division?
               Name :=
                  (if Domain = EW_Prog then
                     To_Program_Space (New_Integer_Division.Id)
                   else
                     New_Division (Get_Base_Type (Current_Type)));
               T :=
                 New_Located_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => Name,
                    Progs    =>
                      (1 => Transform_Expr (Left,
                                            Current_Type,
                                            Domain),
                       2 => Transform_Expr (Right,
                                            Current_Type,
                                            Domain)),
                    Reason   => VC_Division_By_Zero);
               Overflow_Check_Needed := True;
            end;

         when N_Op_Not =>
            if Domain = EW_Term then
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => New_Identifier ("bool_not"),
                    Args     =>
                      (1 => Transform_Expr (Right_Opnd (Expr),
                                            Current_Type,
                                            Domain)));
            else
               T :=
                 New_Not
                   (Right  => Transform_Expr (Right_Opnd (Expr),
                                              Current_Type,
                                              Domain),
                    Domain => Domain);
            end if;
            Current_Type := EW_Bool_Type;

         when N_Op_And =>
            T :=
               New_And_Expr
                 (Left   => Transform_Expr (Left_Opnd (Expr),
                                            Current_Type,
                                            Domain),
                  Right  => Transform_Expr (Right_Opnd (Expr),
                                            Current_Type,
                                            Domain),
                  Domain => Domain);
            Current_Type := EW_Bool_Type;

         when N_Op_Or =>
            T :=
               New_Or_Expr
                 (Left     => Transform_Expr (Left_Opnd (Expr),
                                              Current_Type,
                                              Domain),
                  Right    => Transform_Expr (Right_Opnd (Expr),
                                              Current_Type,
                                              Domain),
                  Domain   => Domain);
            Current_Type := EW_Bool_Type;

         when N_And_Then =>
            T :=
               New_And_Then_Expr
                 (Left   => Transform_Expr (Left_Opnd (Expr),
                                            Current_Type,
                                            Domain),
                  Right  => Transform_Expr (Right_Opnd (Expr),
                                            Current_Type,
                                            Domain),
                  Domain => Domain);
            Current_Type := EW_Bool_Type;

         when N_Or_Else =>
            T :=
               New_Or_Else_Expr
                 (Left   => Transform_Expr (Left_Opnd (Expr),
                                            Current_Type,
                                            Domain),
                  Right  => Transform_Expr (Right_Opnd (Expr),
                                            Current_Type,
                                            Domain),
                  Domain => Domain);
            Current_Type := EW_Bool_Type;

         when N_In =>
            declare
               Subdomain : constant EW_Domain :=
                             (if Domain = EW_Pred then EW_Term else Domain);
            begin
               T :=
                 Range_Expr
                   (Right_Opnd (Expr),
                    Transform_Expr (Left_Opnd (Expr),
                                    EW_Int_Type,
                                    Subdomain),
                    Domain);
            end;

         when N_Quantified_Expression =>
            T := Transform_Quantified_Expression (Expr, Domain, Current_Type);

         when N_Conditional_Expression =>
            declare
               Cond        : constant Node_Id := First (Expressions (Expr));
               Then_Part   : constant Node_Id := Next (Cond);
               Else_Part   : constant Node_Id := Next (Then_Part);
               Cond_Domain : constant EW_Domain :=
                               (if Domain = EW_Term then EW_Pred else Domain);
            begin
               T :=
                  New_Conditional
                     (Ada_Node  => Expr,
                      Domain    => Domain,
                      Condition => +Transform_Expr (Cond,
                                                    EW_Bool_Type,
                                                    Cond_Domain),
                      Then_Part => Transform_Expr (Then_Part,
                                                   Current_Type,
                                                   Domain),
                      Else_Part => Transform_Expr (Else_Part,
                                                   Current_Type,
                                                   Domain));
            end;

         when N_Type_Conversion =>
            return Transform_Expr (Expression (Expr),
                                   Expected_Type,
                                   Domain);

         when N_Unchecked_Type_Conversion =>
            --  Compiler inserted conversions are trusted
            pragma Assert (not Comes_From_Source (Expr));
            return Transform_Expr (Expression (Expr),
                                   Expected_Type,
                                   Domain);

         when N_Function_Call =>
            declare
               Ident : constant W_Identifier_Id :=
                         Transform_Ident (Name (Expr));
               Name  : constant W_Identifier_Id :=
                         (if Domain = EW_Prog then To_Program_Space (Ident)
                          else Logic_Func_Name.Id (Ident));
            begin
               T :=
                 +New_Located_Call
                   (Name     => Name,
                    Progs    => Compute_Call_Args (Expr, Domain),
                    Ada_Node => Expr,
                    Domain   => Domain,
                    Reason   => VC_Precondition);
            end;

         when N_Indexed_Component | N_Selected_Component =>
            T := One_Level_Access (Expr,
                                   Transform_Expr (Prefix (Expr), Domain),
                                   Domain);

         when N_Attribute_Reference =>
            declare
               Aname   : constant Name_Id := Attribute_Name (Expr);
               Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
               Var     : constant Node_Id      := Prefix (Expr);
            begin
               case Attr_Id is
                  when Attribute_Result =>
                     if Result_Name = Why_Empty then
                        T := +New_Result_Term;
                     else
                        T :=
                           New_Unary_Op
                             (Ada_Node => Expr,
                              Op       => EW_Deref,
                              Right    => +Result_Name,
                              Op_Type  => EW_Int,
                              Domain   => Domain);
                     end if;

                  when Attribute_Old =>
                     if Domain = EW_Prog then
                        T := New_Identifier
                                (Symbol => Register_Old_Node (Var),
                                 Domain => Domain);
                     else
                        T :=
                          New_Tagged (Def    => Transform_Expr (Var, Domain),
                                      Tag    => NID (""),
                                      Domain => Domain);
                     end if;

                  when Attribute_First | Attribute_Last | Attribute_Length =>
                     case Ekind (Etype (Var)) is
                        when Array_Kind =>
                           --  ???  Missing support for Array_Type'First
                           --  ???  Missing support of A'First (N)
                           T :=
                             New_Array_Attr
                               (Attribute_Id'Image (Attr_Id),
                                Full_Name (Etype (Var)),
                                Transform_Expr (Var, Domain),
                                Domain);
                           Current_Type := EW_Int_Type;

                        when Enumeration_Kind | Integer_Kind =>
                           T :=
                             +Attr_Name.Id
                               (Full_Name (Etype (Var)),
                                Attribute_Id'Image (Attr_Id));
                           Current_Type := EW_Int_Type;

                        when Real_Kind =>
                           T :=
                             +Attr_Name.Id
                               (Full_Name (Etype (Var)),
                                Attribute_Id'Image (Attr_Id));
                           Current_Type := EW_Real_Type;

                        when others =>
                           --  All possible cases should have been handled
                           --  before this point.
                           pragma Assert (False);
                           null;
                     end case;

               when others =>
                  raise Not_Implemented;
               end case;
            end;

         when N_Case_Expression =>
            T := Case_Expr_Of_Ada_Node (Expr, Domain);

         when N_Expression_With_Actions =>
            if not (Domain = EW_Prog) then
               raise Not_Implemented;
            end if;

            T :=
               +Sequence
                 (Transform_Statements (Actions (Expr)),
                  +Transform_Expr (Expression (Expr),
                                   Expected_Type,
                                   EW_Prog));

         when others =>
            raise Not_Implemented;

      end case;

      declare
         Base_Type : constant W_Base_Type_Id :=
                       (if Overflow_Check_Needed then
                          EW_Abstract (Etype (Expr))
                        else
                          EW_Int_Type);
      begin
         case Domain is
            when EW_Prog =>
               return
                 +Insert_Conversion
                   (Ada_Node  => Expr,
                    From      => Current_Type,
                    To        => Expected_Type,
                    Why_Expr  => +T,
                    Base_Type => Base_Type);

            when EW_Term =>
               return
                 +Insert_Conversion_Term
                   (Ada_Node => Expr,
                    Why_Term => +T,
                    From     => Current_Type,
                    To       => Expected_Type);

            when EW_Pred =>
               return T;

         end case;
      end;
   end Transform_Expr;

   function Transform_Expr (Expr : Node_Id; Domain : EW_Domain)
      return W_Expr_Id is
   begin
      return Transform_Expr (Expr, Type_Of_Node (Expr), Domain);
   end Transform_Expr;

   ---------------------
   -- Transform_Ident --
   ---------------------

   function Transform_Ident (Id : Node_Id) return W_Identifier_Id is
      Ent : Entity_Id;
   begin
      if Nkind (Id) = N_Defining_Identifier then
         Ent := Id;
      else
         Ent := Entity (Id);
      end if;

      return New_Identifier (Full_Name (Ent));
   end Transform_Ident;

   ----------------------------
   -- Transform_Pragma_Check --
   ----------------------------

   function Transform_Pragma_Check (Stmt : Node_Id; Runtime : out W_Prog_Id)
      return W_Pred_Id
   is
      Arg1 : constant Node_Id := First (Pragma_Argument_Associations (Stmt));
      Arg2 : constant Node_Id := Next (Arg1);
      Expr : constant Node_Id := Expression (Arg2);
   begin

      --  Pragma Check generated for Pre/Postconditions are
      --  ignored.

      if Chars (Get_Pragma_Arg (Arg1)) = Name_Precondition
           or else
         Chars (Get_Pragma_Arg (Arg1)) = Name_Postcondition
      then
         Runtime := New_Void (Stmt);
         return New_Literal (Value => EW_True);
      end if;

      if Present (Expr) then
         Runtime := New_Ignore (Prog => +Transform_Expr (Expr, EW_Prog));
         return +Transform_Expr (Expr, EW_Pred);
      else
         raise Program_Error;
      end if;
   end Transform_Pragma_Check;

   -------------------------------------
   -- Transform_Quantified_Expression --
   -------------------------------------

   function Transform_Quantified_Expression
      (Expr         : Node_Id;
       Domain       : EW_Domain;
       Current_Type : out W_Base_Type_Id) return W_Expr_Id
   is
      Index      : W_Identifier_Id;
      Range_E    : Node_Id;
   begin
      Current_Type := Type_Of_Node (Expr);
      Extract_From_Quantified_Expression (Expr, Index, Range_E);
      if Domain = EW_Pred then
         declare
            Conclusion : constant W_Pred_Id :=
                           +Transform_Expr (Condition (Expr),
                                            EW_Pred);
            Hypothesis : W_Pred_Id;
            Quant_Body : W_Pred_Id;
         begin
            Hypothesis := +Range_Expr (Range_E, +Index, EW_Pred);
            Quant_Body :=
               New_Connection
                (Op     => EW_Imply,
                 Left   => +Hypothesis,
                 Right  => +Conclusion);

            if All_Present (Expr) then
               return
                  New_Universal_Quantif
                     (Ada_Node  => Expr,
                      Variables => (1 => Index),
                      Var_Type  => New_Base_Type (Base_Type => EW_Int),
                      Pred      => Quant_Body);
            else
               return
                  New_Existential_Quantif
                     (Ada_Node  => Expr,
                      Variables => (1 => Index),
                      Var_Type  => New_Base_Type (Base_Type => EW_Int),
                      Pred      => Quant_Body);
            end if;
         end;
      elsif Domain = EW_Prog then
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
                                +Transform_Expr (Condition (Expr),
                                                 EW_Prog));
            Range_Cond : W_Prog_Id;
         begin
            Range_Cond := +Range_Expr (Range_E, +Index, EW_Prog);
            Current_Type := EW_Bool_Type;
            return
              +Sequence
                (New_Binding
                   (Name    => Index,
                    Def     =>
                      +New_Simpl_Any_Prog
                        (New_Base_Type (Base_Type => EW_Int)),
                    Context =>
                      New_Conditional
                        (Domain    => EW_Prog,
                         Condition => +Range_Cond,
                         Then_Part => +Why_Expr)),
                 New_Assume_Statement
                   (Ada_Node    => Expr,
                    Return_Type => New_Base_Type (Base_Type => EW_Bool),
                    Pred        =>
                      +Transform_Expr (Expr, EW_Pred)));
         end;
      else
         raise Not_Implemented;
      end if;
   end Transform_Quantified_Expression;

   -------------------------
   -- Transform_Statement --
   -------------------------

   function Transform_Statement (Stmt : Node_Id) return W_Prog_Id is
   begin
      --  ??? TBD: complete this function for the remaining cases
      case Nkind (Stmt) is
         when N_Null_Statement =>
            return New_Void (Stmt);

         when N_Assignment_Statement =>

            return Transform_Assignment_Statement (Stmt);

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
                  declare
                     Return_Type : constant W_Base_Type_Id :=
                                     Type_Of_Node (Etype (Return_Applies_To
                                       (Return_Statement_Entity (Stmt))));
                  begin
                     Result_Stmt :=
                       New_Assignment
                         (Ada_Node => Stmt,
                          Name     => Result_Name,
                          Value    =>
                            +Transform_Expr (Expression (Stmt),
                                             Return_Type,
                                             EW_Prog));
                     return Sequence (Result_Stmt, Raise_Stmt);
                  end;
               else
                  return Raise_Stmt;
               end if;
            end;

         when N_Procedure_Call_Statement =>
            return
              +New_Located_Call
                (Ada_Node => Stmt,
                 Name     =>
                   To_Program_Space (Transform_Ident (Name (Stmt))),
                 Progs    => Compute_Call_Args (Stmt, EW_Prog),
                 Domain   => EW_Prog,
                 Reason   => VC_Precondition);

         when N_If_Statement =>
            declare
               Tail : W_Prog_Id :=
                        Transform_Statements (Else_Statements (Stmt));
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
                          +New_Simpl_Conditional
                            (Condition =>
                               Transform_Expr (Condition (Cur), EW_Prog),
                             Then_Part =>
                               +Transform_Statements (Then_Statements (Cur)),
                             Else_Part => +Tail,
                             Domain    => EW_Prog);
                        Prev (Cur);
                     end loop;
                  end;
               end if;

               --  Finish by putting the main if-then-else on top.

               return
                 +New_Simpl_Conditional
                   (Condition => Transform_Expr (Condition (Stmt),
                                                 EW_Prog),
                    Then_Part =>
                      +Transform_Statements (Then_Statements (Stmt)),
                    Else_Part => +Tail,
                    Domain    => EW_Prog);
            end;

         when N_Raise_xxx_Error =>
            raise Not_Implemented;

         when N_Object_Declaration =>
            return Assignment_of_Obj_Decl (Stmt);

         when N_Loop_Statement =>
            return Transform_Loop_Statement (Stmt);

         when N_Exit_Statement =>
            return Transform_Exit_Statement (Stmt);

         when N_Case_Statement =>
            return +Case_Expr_Of_Ada_Node (Stmt, EW_Prog);

         when N_Pragma =>
            case Get_Pragma_Id (Pragma_Name (Stmt)) is
               when Pragma_Annotate =>
                  return New_Void (Stmt);

               when Pragma_Check =>
                  declare
                     Check_Expr : W_Prog_Id;
                     Pred : constant W_Pred_Id :=
                        Transform_Pragma_Check (Stmt, Check_Expr);
                  begin
                     if Is_False_Boolean (+Pred) then
                        return
                          +New_Located_Expr
                            (Ada_Node => Stmt,
                             Expr     => +New_Identifier ("absurd"),
                             Reason   => VC_Assert,
                             Domain   => EW_Prog);
                     elsif Is_True_Boolean (+Pred) then
                        return New_Void (Stmt);
                     elsif Check_Expr /= Why_Empty then
                        return
                          Sequence (Check_Expr,
                                    New_Located_Assert (Stmt, Pred));
                     else
                        return New_Located_Assert (Stmt, Pred);
                     end if;
                  end;

               when others =>
                  raise Not_Implemented;

            end case;

         when others =>
            raise Not_Implemented;
      end case;
   end Transform_Statement;

   --------------------------
   -- Transform_Statements --
   --------------------------

   function Transform_Statements
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
         Result := Sequence (Result, Transform_Statement (Cur_Stmt));
         Next (Cur_Stmt);
      end loop;
      return Result;
   end Transform_Statements;

   ---------------------------
   -- Transform_Static_Expr --
   ---------------------------

   function Transform_Static_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id) return W_Term_Id is
   begin
      if Present (Expr) and then Is_Static_Expression (Expr) then
         return +Transform_Expr (Expr, Expected_Type, EW_Term);
      else
         return Why_Empty;
      end if;
   end Transform_Static_Expr;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return Entity_Id is
   begin
      if Nkind (N) in N_Entity then
         if Ekind (N) in Type_Kind then
            return N;
         else
            return Etype (N);
         end if;
      elsif Nkind (N) in N_Identifier | N_Expanded_Name then
         return Etype (Entity (N));
      else
         return Etype (N);
      end if;
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return String
   is
      E : constant Entity_Id := Type_Of_Node (N);
   begin
      if E = Standard_Boolean then
         return Why_Scalar_Type_Name (EW_Bool);
      else
         return Full_Name (E);
      end if;
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return W_Base_Type_Id
   is
      E : constant Entity_Id := Type_Of_Node (N);
   begin
      if E = Standard_Boolean then
         return EW_Bool_Type;
      else
         return EW_Abstract (E);
      end if;
   end Type_Of_Node;

end Gnat2Why.Expr;
