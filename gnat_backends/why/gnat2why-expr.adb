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
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Gen.Arrays;        use Why.Gen.Arrays;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Preds;         use Why.Gen.Preds;
with Why.Gen.Progs;         use Why.Gen.Progs;
with Why.Gen.Terms;         use Why.Gen.Terms;
with Why.Conversions;       use Why.Conversions;
with Why.Types;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Driver;       use Gnat2Why.Driver;
with Gnat2Why.Expr;         use Gnat2Why.Expr;

package body Gnat2Why.Expr is

   Result_String : constant String := "___result";
   --  The internal name for the result of an expression

   function Case_Expr_Of_Ada_Node (N : Node_Id; Domain : EW_Domain)
      return W_Expr_Id;
   --  Build Case expression of Ada Node.

   function Compute_Call_Args (Call : Node_Id; Domain : EW_Domain)
      return W_Expr_Array;
   --  Compute arguments for a function call or procedure call. The node in
   --  argument must have a "Name" field and a "Parameter_Associations" field.

   procedure Compute_Invariant
      (Loop_Body  : List_Id;
       Pred       : out W_Pred_Id;
       Split_Node : out Node_Id);
   --  Given a list of statements (a loop body), construct a predicate that
   --  corresponds to the conjunction of all assertions at the beginning of
   --  the list. The out parameter Split_Node is set to the last node that is
   --  an assertion.
   --  If there are no assertions, we set Split_Node to N_Empty and we return
   --  True.

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

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id;
   --  Return the Defining_Identifier of the loop that belongs to an exit
   --  statement.

   function Predicate_Of_Pragma_Check (N : Node_Id) return W_Pred_Id;
   --  Compute a Why predicate from a node of kind Pragma Check. Raise
   --  Not_Implemented if it is not a Pragma Check.

   function Range_Expr (N : Node_Id; T : W_Expr_Id; Domain : EW_Domain)
      return W_Expr_Id;
   --  Given an N_Range node N and a Why expr T, create an expression
   --  low <= T <= high
   --  where "low" and "high" are the lower and higher bounds of N.

   function Transform_Quantified_Expression
      (Expr         : Node_Id;
       Domain       : EW_Domain;
       Current_Type : out Why_Type) return W_Expr_Id;

   function Transform_Statement (Stmt : Node_Id) return W_Prog_Id;
   --  Translate a single Ada statement into a Why expression

   function Why_Binop_Of_Ada_Op (Op : N_Binary_Op) return EW_Binary_Op;
   --  Convert an Ada binary operator to a Why term symbol

   function Why_Expr_Of_Ada_Enum
     (Enum         : Node_Id;
      Current_Type : out Why_Type;
      Domain       : EW_Domain)
      return W_Expr_Id;
   --  Translate an Ada enumeration literal to Why. There are a number of
   --  special cases, so its own function is appropriate.

   function Why_Rel_Of_Ada_Op (Op : N_Op_Compare) return EW_Relation;
   --  Convert an Ada comparison operator to a Why relation symbol

   function Wrap_Loop
      (Loop_Body : W_Prog_Id;
       Condition : W_Prog_Id;
       Loop_Name : String;
       Invariant : W_Pred_Id;
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
                         +Transform_Expr (Rexpr,
                                                Type_Of_Node (Lvalue),
                                                EW_Prog);
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
                  Eq      : constant W_Pred_Id :=
                              New_Relation
                                (Op      => EW_Eq,
                                 Op_Type => Get_EW_Type (Lvalue),
                                 Left    => +Tmp_Var,
                                 Right   => +L_Id);
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
               return +Why_Expr_Of_Ada_Stmts (Statements (N));

            when others =>
               raise Unexpected_Node;

         end  case;
      end Branch_Expr;

      Cur_Case     : Node_Id := Last (Alternatives (N));
      Matched_Expr : constant W_Expr_Id :=
                       Transform_Expr (Expression (N),
                                             EW_Int_Type,
                                             Domain);

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
                             (Domain => Domain,
                              Value  => EW_False);
         begin
            while Present (Cur_Choice) loop
               C := New_Or_Else_Expr
                      (C,
                       Equal_To (Matched_Expr, Cur_Choice, Domain),
                       Domain);
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
                        +Why_Expr_Of_Ada_Stmts (Statements (Cur_Case));

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
                  Why_Args (Cnt) := +Why_Ident_Of_Ada_Ident (Actual);

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

   -----------------------
   -- Compute_Invariant --
   -----------------------

   procedure Compute_Invariant
      (Loop_Body  : List_Id;
       Pred       : out W_Pred_Id;
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
                 +New_And_Expr
                   (Left => +Pred,
                    Right => +Predicate_Of_Pragma_Check (Cur_Stmt),
                    Domain => EW_Pred);

            when others =>
               exit;
         end case;

         Split_Node := Cur_Stmt;
         Nlists.Next (Cur_Stmt);
      end loop;
   end Compute_Invariant;

   --------------
   -- Equal_To --
   --------------

   function Equal_To
     (E      : W_Expr_Id;
      N      : Node_Id;
      Domain : EW_Domain)
     return W_Expr_Id is
   begin
      case Nkind (N) is
         when N_Identifier
           | N_Real_Literal
           | N_Integer_Literal =>
            declare
               BT : constant Why_Type := Base_Why_Type (N);
            begin
               return
                 New_Comparison
                 (Cmp       => EW_Eq,
                  Left      => E,
                  Right     => Transform_Expr (N, BT, Domain),
                  Arg_Types => BT.Kind,
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
                                                         Domain),
                      Arg_Types => EW_Int,
                      Right     => E,
                      Domain    => Domain),
                 Right =>
                   New_Comparison
                     (Cmp       => EW_Le,
                      Left      => E,
                      Right     => Transform_Expr (High_Bound (N),
                                                         EW_Int_Type,
                                                         Domain),
                      Arg_Types => EW_Int,
                      Domain    => Domain),
                 Domain => Domain);

         when N_Others_Choice =>
            return New_Literal (Value => EW_True);

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

   function Predicate_Of_Pragma_Check (N : Node_Id) return W_Pred_Id is
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
               return +Transform_Expr (Expression (Arg2), EW_Pred);

            else
               raise Program_Error;
            end if;
         end;

      else
         raise Not_Implemented;
      end if;
   end Predicate_Of_Pragma_Check;

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

   -------------------------------------
   -- Transform_Quantified_Expression --
   -------------------------------------

   function Transform_Quantified_Expression
      (Expr         : Node_Id;
       Domain       : EW_Domain;
       Current_Type : out Why_Type) return W_Expr_Id
   is
      Index      : W_Identifier_Id;
      Range_E    : Node_Id;
   begin
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
                (Domain => EW_Pred,
                 Op     => EW_Imply,
                 Left   => +Hypothesis,
                 Right  => +Conclusion);

            if All_Present (Expr) then
               return
                  New_Universal_Quantif
                     (Domain    => EW_Pred,
                      Ada_Node  => Expr,
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
            Range_Cond :=
               +Range_Expr
                 (Range_E,
                  New_Unary_Op
                    (Domain => EW_Prog,
                     Op     => EW_Deref,
                     Right  => +Index),
                  EW_Prog);
            Current_Type := EW_Bool_Type;
            return
              +Sequence
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
                      +Transform_Expr (Expr, EW_Pred)));
         end;
      else
         raise Not_Implemented;
      end if;
   end Transform_Quantified_Expression;

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

   function Type_Of_Node (N : Node_Id) return Why_Type
   is
      E : constant Entity_Id := Type_Of_Node (N);
   begin
      if E = Standard_Boolean then
         return EW_Bool_Type;
      else
         return EW_Abstract (E);
      end if;
   end Type_Of_Node;

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
         Current_Type := (Kind => EW_Bool);
         return New_Literal (Value => EW_True, Domain => Domain);
      end if;

      if Entity (Enum) = Standard_False then
         Current_Type := (Kind => EW_Bool);
         return New_Literal (Value => EW_False, Domain => Domain);
      end if;

      --  In the case of a subtype of an enumeration, we need to insert a
      --  conversion. We do so here by modifying the Current_Type; the
      --  conversion itself will be inserted by Transform_Expr.

      case Ekind (Etype (Enum)) is
         when E_Enumeration_Subtype =>
            Current_Type := EW_Abstract (Etype (Entity (Enum)));

         when others =>
            null;
      end case;

      return +Why_Ident_Of_Ada_Ident (Enum);
   end Why_Expr_Of_Ada_Enum;

   --------------------------
   -- Transform_Expr --
   --------------------------

   function Transform_Expr
     (Expr          : Node_Id;
      Expected_Type : Why_Type;
      Domain        : EW_Domain) return W_Expr_Id
   is
      T                     : W_Expr_Id;
      Current_Type          : Why_Type := Type_Of_Node (Expr);
      Overflow_Check_Needed : Boolean := False;
   begin

      --  Expressions that cannot be translated to predicates directly are
      --  translated to (boolean) terms, and compared to "True"

      if Domain = EW_Pred and then
         not (Nkind (Expr) in N_Op_Compare | N_Op_Not | N_Op_And | N_And_Then
         | N_Op_Or | N_Or_Else | N_In | N_Conditional_Expression |
         N_Quantified_Expression) then
         return
           New_Relation
             (Ada_Node => Expr,
              Domain   => EW_Pred,
              Op_Type  => EW_Bool,
              Left     => +Transform_Expr (Expr, EW_Bool_Type, EW_Term),
              Right    => New_Literal (Value => EW_True, Domain => EW_Term),
              Op       => EW_Eq);
      end if;

      case Nkind (Expr) is
         when N_Integer_Literal =>
            T :=
              New_Integer_Constant
                (Domain   => Domain,
                 Ada_Node => Expr,
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
                         (Domain   => Domain,
                          Ada_Node => Expr,
                          Value    => Realval (Expr));
               end;

            else
               T :=
                 New_Real_Constant
                   (Domain   => Domain,
                    Ada_Node => Expr,
                    Value    => Realval (Expr));
            end if;

            Current_Type := EW_Real_Type;

         when N_Character_Literal =>

            T :=
              New_Integer_Constant (Ada_Node => Expr,
                                    Value    => Char_Literal_Value (Expr),
                                    Domain   => Domain);
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
               Id : constant W_Identifier_Id := Why_Ident_Of_Ada_Ident (Expr);
            begin
               case Ekind (Entity (Expr)) is
                  --  First treat special cases

                  when E_Enumeration_Literal =>
                     T := Why_Expr_Of_Ada_Enum (Expr, Current_Type, Domain);

                  when others =>
                     if Is_Mutable (Entity (Expr)) then
                        T :=
                          New_Unary_Op
                            (Ada_Node => Expr,
                             Domain   => Domain,
                             Op       => EW_Deref,
                             Right    => +Id);
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
               BT        : constant Why_Type := Base_Why_Type (Left, Right);
               Subdomain : constant EW_Domain :=
                             (if Domain = EW_Pred then EW_Term else Domain);
            begin
               T :=
                 New_Comparison
                   (Cmp       => Why_Rel_Of_Ada_Op (Nkind (Expr)),
                    Left      => Transform_Expr (Left, BT, Subdomain),
                    Right     => Transform_Expr (Right, BT, Subdomain),
                    Arg_Types => BT.Kind,
                    Domain    => Domain);
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
                      +Transform_Expr (Right, Current_Type, Domain));
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
                    Domain   => Domain,
                    Left     => Transform_Expr (Left,
                                                      Current_Type,
                                                      Domain),
                    Right    => Transform_Expr (Right,
                                                      Current_Type,
                                                      Domain),
                    Op       => Why_Binop_Of_Ada_Op (Nkind (Expr)),
                    Op_Type  => Current_Type.Kind);
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
                     New_Division (Current_Type.Kind));
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
               Cond      : constant Node_Id := First (Expressions (Expr));
               Then_Part : constant Node_Id := Next (Cond);
               Else_Part : constant Node_Id := Next (Then_Part);
               Subdomain : constant EW_Domain :=
                             (if Domain = EW_Pred and then not Is_Why3
                              then EW_Term
                              else Domain);
            begin
               T :=
                  New_Conditional
                     (Ada_Node => Expr,
                      Condition => +Transform_Expr (Cond,
                                                          EW_Bool_Type,
                                                          Subdomain),
                      Then_Part => Transform_Expr (Then_Part,
                                                         Expected_Type,
                                                         Domain),
                      Else_Part => Transform_Expr (Else_Part,
                                                         Expected_Type,
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

         when N_Selected_Component =>
            T :=
              New_Call
                (Domain => Domain,
                 Name   =>
                   Record_Getter_Name.Id
                     (Full_Name (Entity (Selector_Name (Expr)))),
                 Args => (1 => Transform_Expr (Prefix (Expr),
                                                     Domain)));

         when N_Function_Call =>
            declare
               Ident : constant W_Identifier_Id :=
                         Why_Ident_Of_Ada_Ident (Name (Expr));
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

         when N_Indexed_Component =>
            declare
               N      : Integer := 1;
               Ar     : constant Node_Id := Prefix (Expr);
               Index  : Node_Id := First (Expressions (Expr));
               T_Name : constant String := Type_Of_Node (Ar);
            begin
               T := Transform_Expr (Ar, Domain);
               while Present (Index) loop
                  T :=
                    New_Array_Access
                     (Ada_Node => Expr,
                      Domain   => Domain,
                      Type_Name =>
                        (if N = 1 then T_Name
                         else T_Name & "___" & Int_Image (N)),
                      Ar        => T,
                      Index     =>
                        Transform_Expr (Index, EW_Int_Type, Domain));
                  Next (Index);
                  N := N + 1;
               end loop;
            end;

         when N_Attribute_Reference =>
            declare
               Aname   : constant Name_Id := Attribute_Name (Expr);
               Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
               Var     : constant Node_Id      := Prefix (Expr);
            begin
               case Attr_Id is
                  when Attribute_Result =>
                     if Domain = EW_Term then
                        T := +New_Result_Term;
                     end if;
                     if Domain = EW_Prog then
                        T := +New_Identifier (Result_String);
                     end if;

                  when Attribute_Old =>
                     if Domain = EW_Prog then
                        raise Not_Implemented;
                     end if;

                     T := +New_Old_Ident (Why_Ident_Of_Ada_Ident (Var));

                  when Attribute_First =>
                     T :=
                       New_Array_First
                         (Full_Name (Etype (Var)),
                          Transform_Expr (Var, Domain),
                          Domain);
                     Current_Type := EW_Int_Type;

                  when Attribute_Last =>
                     T :=
                       New_Array_Last
                         (Full_Name (Etype (Var)),
                          Transform_Expr (Var, Domain),
                          Domain);
                     Current_Type := EW_Int_Type;

                  when Attribute_Length =>
                     T :=
                       New_Array_Length
                         (Full_Name (Etype (Var)),
                          Transform_Expr (Var, Domain),
                          Domain);
                     Current_Type := EW_Int_Type;

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
                 (Why_Expr_Of_Ada_Stmts (Actions (Expr)),
                  +Transform_Expr (Expression (Expr),
                                         Expected_Type,
                                         EW_Prog));

         when others =>
            raise Not_Implemented;

      end case;
      declare
         Base_Type : constant Why_Type :=
            (if Overflow_Check_Needed then
               EW_Abstract (Etype (Etype (Expr)))
            else
               EW_Int_Type);
      begin
         case Domain is
            when EW_Prog =>
               return
                 +Insert_Conversion
                   (Ada_Node              => Expr,
                    From                  => Current_Type,
                    To                    => Expected_Type,
                    Why_Expr              => +T,
                    Base_Type             => Base_Type);

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

   --------------------------
   -- Transform_Statement --
   --------------------------

   function Transform_Statement (Stmt : Node_Id) return W_Prog_Id is
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
                            +Transform_Expr
                              (Expression (Stmt),
                               Type_Of_Node (Lvalue),
                               EW_Prog));

                  when N_Indexed_Component =>
                     declare
                        Pre : constant Node_Id := Prefix (Lvalue);
                     begin
                        if Number_Dimensions (Etype (Pre)) > 1 then
                           raise Not_Implemented;
                        else
                           return
                             New_Array_Update_Prog
                               (Ada_Node  => Stmt,
                                Type_Name => Type_Of_Node (Pre),
                                Ar        => Why_Ident_Of_Ada_Ident (Pre),
                                Index     =>
                                  +Transform_Expr
                                    (First (Expressions (Lvalue)),
                                     EW_Int_Type,
                                     EW_Prog),
                                Value     =>
                                  +Transform_Expr
                                    (Expression (Stmt),
                                     Type_Of_Node
                                       (Component_Type (Etype (Pre))),
                                     EW_Prog));
                        end if;
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
                  declare
                     Return_Type : constant Why_Type :=
                                     Type_Of_Node (Etype (Return_Applies_To
                                       (Return_Statement_Entity (Stmt))));
                  begin
                     Result_Stmt :=
                       New_Assignment
                         (Ada_Node => Stmt,
                          Name     => New_Result_Temp_Identifier.Id,
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
                   To_Program_Space (Why_Ident_Of_Ada_Ident (Name (Stmt))),
                 Progs    => Compute_Call_Args (Stmt, EW_Prog),
                 Domain   => EW_Prog,
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
                          +New_Simpl_Conditional
                            (Condition =>
                               Transform_Expr (Condition (Cur), EW_Prog),
                             Then_Part =>
                               +Why_Expr_Of_Ada_Stmts (Then_Statements (Cur)),
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
                      +Why_Expr_Of_Ada_Stmts (Then_Statements (Stmt)),
                    Else_Part => +Tail,
                    Domain    => EW_Prog);
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
               Invariant    : W_Pred_Id;
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
                         Condition => New_Literal (Value => EW_True),
                         Loop_Name => Loop_Name,
                         Invariant => Invariant,
                         Inv_Node  => Split_Node);

               elsif
                 Nkind (Iterator_Specification (Scheme)) = N_Empty
                   and then
                 Nkind (Loop_Parameter_Specification (Scheme)) = N_Empty
               then
                  --  A while loop
                  declare
                     Enriched_Inv : constant W_Pred_Id :=
                                      +New_And_Expr
                                        (Left   => +Invariant,
                                         Right  =>
                                           Transform_Expr
                                             (Condition (Scheme), EW_Pred),
                                         Domain => EW_Pred);
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
                          +Transform_Expr (Condition (Scheme), EW_Prog),
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
                                      Discrete_Subtype_Definition
                                        (LParam_Spec);
                     Loop_Index   : constant W_Identifier_Id :=
                                      New_Identifier
                                        (Full_Name
                                           (Defining_Identifier
                                             (LParam_Spec)));
                     Index_Deref  : constant W_Prog_Id :=
                                      New_Unary_Op
                                        (Ada_Node => Stmt,
                                         Domain   => EW_Prog,
                                         Op       => EW_Deref,
                                         Right    => +Loop_Index);
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
                                         Name     => Loop_Index,
                                         Value    => Addition);
                     Enriched_Inv : constant W_Pred_Id :=
                                      +New_And_Expr
                                        (Left  => +Invariant,
                                         Right =>
                                           Range_Expr
                                            (Loop_Range,
                                             New_Unary_Op
                                               (Domain   => EW_Term,
                                               Op       => EW_Deref,
                                               Right    => +Loop_Index),
                                             EW_Pred),
                                         Domain => EW_Pred);
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
                                           +Range_Expr
                                             (Loop_Range,
                                              +Index_Deref,
                                              EW_Prog),
                                         Loop_Name    => Loop_Name,
                                         Invariant    => Enriched_Inv,
                                         Inv_Node     => Inv_Node);
                     Low          : constant Node_Id :=
                                      Low_Bound
                                        (Get_Range
                                          (Discrete_Subtype_Definition
                                            (LParam_Spec)));
                  begin
                     return
                       New_Binding_Ref
                         (Name    => Loop_Index,
                          Def     => +Transform_Expr (Low,
                                                            EW_Int_Type,
                                                            EW_Prog),
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
                          +Transform_Expr (Condition (Stmt), EW_Prog),
                       Then_Part => +Raise_Stmt);
               end if;
            end;

         when N_Case_Statement =>
            return +Case_Expr_Of_Ada_Node (Stmt, EW_Prog);

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
   end Transform_Statement;

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
         Result := Sequence (Result, Transform_Statement (Cur_Stmt));
         Next (Cur_Stmt);
      end loop;
      return Result;
   end Why_Expr_Of_Ada_Stmts;

   ----------------------------
   -- Why_Ident_Of_Ada_Ident --
   ----------------------------

   function Why_Ident_Of_Ada_Ident (Id : Node_Id) return W_Identifier_Id is
      Ent : Entity_Id;
   begin
      if Nkind (Id) = N_Defining_Identifier then
         Ent := Id;
      else
         Ent := Entity (Id);
      end if;

      return New_Identifier (Full_Name (Ent));
   end Why_Ident_Of_Ada_Ident;

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

   ---------------
   -- Wrap_Loop --
   ---------------

   function Wrap_Loop
      (Loop_Body : W_Prog_Id;
       Condition : W_Prog_Id;
       Loop_Name : String;
       Invariant : W_Pred_Id;
       Inv_Node  : Node_Id)
      return W_Prog_Id
   is
      Entire_Body : constant W_Prog_Id :=
                      Sequence
                        (Loop_Body,
                         New_Conditional
                           (Domain    => EW_Prog,
                            Condition =>
                              New_Not (Right => +Condition, Domain => EW_Prog),
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

end Gnat2Why.Expr;
