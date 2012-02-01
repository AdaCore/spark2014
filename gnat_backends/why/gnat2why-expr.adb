------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - E X P R                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Ada.Containers;                     use Ada.Containers;
with Ada.Containers.Hashed_Maps;

with Einfo;              use Einfo;
with Namet;              use Namet;
with Nlists;             use Nlists;
with Sem_Eval;           use Sem_Eval;
with Sem_Util;           use Sem_Util;
with Snames;             use Snames;
with Stand;              use Stand;
with Uintp;              use Uintp;
with Urealp;             use Urealp;
with VC_Kinds;           use VC_Kinds;
with Eval_Fat;

with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;

with Why;                   use Why;
with Why.Inter;             use Why.Inter;
with Why.Unchecked_Ids;     use Why.Unchecked_Ids;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Accessors;   use Why.Atree.Accessors;
with Why.Atree.Tables;      use Why.Atree.Tables;
with Why.Atree.Mutators;    use Why.Atree.Mutators;
with Why.Gen.Arrays;        use Why.Gen.Arrays;
with Why.Gen.Binders;       use Why.Gen.Binders;
with Why.Gen.Decl;          use Why.Gen.Decl;
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

   ---------------------
   -- Local Variables --
   ---------------------

   function Node_Hash (X : Node_Id) return Hash_Type is (Hash_Type (X));

   package Ada_To_Why is new Hashed_Maps (Key_Type        => Node_Id,
                                          Element_Type    => Why_Node_Id,
                                          Hash            => Node_Hash,
                                          Equivalent_Keys => "=",
                                          "="             => "=");

   Ada_To_Why_Term : array (Boolean) of Ada_To_Why.Map;
   --  Mappings from Ada nodes to their Why translation as a term, with the
   --  Boolean index of the array denoting whether Ref_Allowed was True or
   --  False when building the term.

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Apply_Modulus
      (E                     : Entity_Id;
       T                     : W_Expr_Id;
       Domain                : EW_Domain;
       Overflow_Check_Needed : in out Boolean)
       return W_Expr_Id;
   --  Apply a modulus on T, where the modulus is defined by the Entity N
   --  which must be a modular type. If E is not a modular type, set
   --  Overflow_Check_Needed to True and return T unchanged.

   function Case_Expr_Of_Ada_Node
     (N             : Node_Id;
      Expected_Type : W_Base_Type_OId := Why_Empty;
      Domain        : EW_Domain;
      Params        : Translation_Params) return W_Expr_Id;
   --  Build Case expression of Ada Node.

   function Compute_Call_Args
     (Call        : Node_Id;
      Domain      : EW_Domain;
      Nb_Of_Refs  : out Natural;
      Params      : Translation_Params) return W_Expr_Array;
   --  Compute arguments for a function call or procedure call. The node in
   --  argument must have a "Name" field and a "Parameter_Associations" field.
   --  Nb_Of_Refs is the number of ref arguments that could not be
   --  translated "as is" (because of a type mismatch) and for which
   --  Insert_Ref_Context must be called.

   function Needs_Temporary_Ref
     (Actual : Node_Id;
      Formal : Node_Id)
     return Boolean;
   --  True if the parameter passing needs a temporary ref to be performed.

   function Insert_Ref_Context
     (Params     : Translation_Params;
      Ada_Call   : Node_Id;
      Why_Call   : W_Prog_Id;
      Nb_Of_Refs : Positive) return W_Prog_Id;
   --  Considering a call to an Ada subprogram; Ada_Call being its node
   --  in the Ada syntax tree, and Why_Call its corresponding call in the
   --  Why syntax tree:
   --
   --  For all "out"/"in out" parameters that need a conversion, generate
   --  the whole context around the call, using a temporary variable
   --  which is named after the corresponding formal. e.g. something of the
   --  form:
   --
   --   let formal := ref (to_formal_type_ (from_actual_type (!actual))) in
   --    (<why_call> ;
   --     actual := to_actual_type_ (from_formal_type (!formal))
   --
   --  Nb_Of_Refs should be set to the number of such parameters in Ada_Call.

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
     (N           : Node_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Translation_Params) return W_Expr_Id;
   --  Compute an access expression for record and array accesses without
   --  considering subexpressions. [N] represents the Ada node of the access,
   --  and [Expr] the Why expression of the prefix.

   function One_Level_Update
     (N           : Node_Id;
      Pref        : W_Expr_Id;
      Value       : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Translation_Params) return W_Expr_Id;
   --  same as One_Level_Access, but for updates

   function Transform_Block_Statement (N : Node_Id) return W_Prog_Id;

   function Transform_Discrete_Choice
     (Choice      : Node_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Translation_Params) return W_Expr_Id;
   --  For an expression Expr of a type EW_Int and a discrete Choice, build
   --  the expression that Expr belongs to the range expressed by Choice.

   function Transform_Quantified_Expression
     (Expr         : Node_Id;
      Domain       : EW_Domain;
      Params       : Translation_Params;
      Current_Type : out W_Base_Type_Id) return W_Expr_Id;

   function Transform_Statement (Stmt : Node_Id) return W_Prog_Id;

   procedure Transform_Array_Aggregate
     (Params : Translation_Params;
      Typ    : Entity_Id;
      Id   : W_Identifier_Id;
      Expr : Node_Id);
   --  Transform an aggregate Expr into the equivalent Why terms, both with and
   --  w/o references allowed. The results of this translation are stored in
   --  Ada_To_Why_Term, so that the necessary function and axiom are generated
   --  only once per source aggregate.
   --
   --  A logic function F is generated to replace the aggregate with a call. It
   --  takes in parameters all values of references used in the aggregate:
   --     function F (<params>) : <type of aggregate>
   --
   --  An axiom A gives the value of the function:
   --     axiom A:
   --        forall R:<type of aggregate>. forall <params>.
   --           R = F(<params>) -> <predicate for the aggregate R>

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id;
   --  Translate a single Ada statement into a Why expression

   function New_Assignment
     (Ada_Node : Node_Id := Empty;
      Lvalue   : Node_Id;
      Expr     : W_Prog_Id) return W_Prog_Id;
   --  Translate an assignment of the form "Lvalue := Expr",
   --  using Ada_Node for its source location.

   function Transform_Attr
     (Expr          : Node_Id;
      Domain        : EW_Domain;
      Current_Type  : out W_Base_Type_Id;
      Params        : Translation_Params) return W_Expr_Id;

   procedure Transform_String_Literal
     (Params : Translation_Params;
      N      : Node_Id);

   function Transform_Array_Component_Associations
     (Expr        : Node_Id;
      Typ         : Entity_Id;
      Id          : W_Identifier_Id;
      Params      : Translation_Params) return W_Pred_Id;

   function Transform_Record_Component_Associations
     (Domain      : EW_Domain;
      Typ         : Entity_Id;
      Assocs      : List_Id;
      Params      : Translation_Params) return W_Field_Association_Array;

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

   -------------------
   -- Apply_Modulus --
   -------------------

   function Apply_Modulus
      (E                     : Entity_Id;
       T                     : W_Expr_Id;
       Domain                : EW_Domain;
       Overflow_Check_Needed : in out Boolean)
      return W_Expr_Id
   is
   begin
      if Is_Modular_Integer_Type (E) then
         return
            New_Call (Name => New_Integer_Mod.Id,
                      Domain => Domain,
                      Args =>
                       (1 => T,
                        2 => New_Integer_Constant
                                (Value => Modulus (E))));
      else
         Overflow_Check_Needed := True;
         return T;
      end if;
   end Apply_Modulus;

   ----------------------------
   -- Assignment_of_Obj_Decl --
   ----------------------------

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
                                          EW_Prog,
                                          Params => Body_Params);
            L_Name   : constant String := Full_Name (Lvalue);
            L_Id     : constant W_Identifier_Id :=
              New_Identifier (N, L_Name);
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

   ------------------------------
   -- Assume_of_Scalar_Subtype --
   ------------------------------

   function Assume_of_Scalar_Subtype
     (Params : Translation_Params;
      N      : Entity_Id;
      Base   : Entity_Id) return W_Prog_Id
   is
      Rng              : constant Node_Id := Get_Range (N);
      Why_Base         : constant W_Base_Type_Id := Base_Why_Type (N);
      Why_Base_EW      : constant EW_Type := Get_EW_Type (N);
      Low_Expr         : constant W_Term_Id :=
         +Transform_Expr (Low_Bound (Rng), Why_Base, EW_Term, Params);
      High_Expr        : constant W_Term_Id :=
         +Transform_Expr (High_Bound (Rng), Why_Base, EW_Term, Params);
      First_Term       : constant W_Term_Id :=
        New_Attribute_Expr (N, Attribute_First);
      Last_Term        : constant W_Term_Id :=
        New_Attribute_Expr (N, Attribute_Last);
      Rel_First        : constant W_Pred_Id :=
         New_Relation
           (Op_Type  => EW_Bool,
            Left     => +Low_Expr,
            Right    => +First_Term,
            Op       => EW_Eq);
      Rel_Last         : constant W_Pred_Id :=
         New_Relation
           (Op_Type  => EW_Bool,
            Left     => +High_Expr,
            Right    => +Last_Term,
            Op       => EW_Eq);
      First_In_Range   : constant W_Pred_Id :=
         New_Relation
           (Op_Type  => Why_Base_EW,
            Left     => +Low_Expr,
            Right    => New_Attribute_Expr (Base, Attribute_First),
            Op       => EW_Ge);
      Last_In_Range    : constant W_Pred_Id :=
         New_Relation
           (Op_Type  => Why_Base_EW,
            Left     => +High_Expr,
            Right    => New_Attribute_Expr (Base, Attribute_Last),
            Op       => EW_Le);
      First_Le_Last    : constant W_Pred_Id :=
         New_Relation
           (Op_Type  => Why_Base_EW,
            Left     => +Low_Expr,
            Right    => +High_Expr,
            Op       => EW_Le);
      Precond          : constant W_Pred_Id :=
         +New_Connection
           (Op     => EW_Imply,
            Left   => +First_Le_Last,
            Right  =>
              +New_And_Expr
                 (Domain => EW_Pred,
                  Left   => +First_In_Range,
                  Right => +Last_In_Range));
      Any_Expr        : constant W_Prog_Id :=
         New_Any_Expr
           (Any_Type =>
              New_Computation_Type
                 (Domain => EW_Prog,
                  Result =>
                     New_Result (New_Base_Type (Base_Type => EW_Unit)),
                  Pre   => +Precond,
                  Post   =>
                    +New_And_Expr
                      (Domain => EW_Pred,
                       Left   => +Rel_First,
                       Right  => +Rel_Last)));
   begin
      return
        +New_Located_Expr
          (Ada_Node => N,
           Domain   => EW_Prog,
           Reason   => VC_Range_Check,
           Expr     => +Any_Expr);
   end Assume_of_Scalar_Subtype;

   ----------------------------------
   -- Assume_of_Subtype_Indication --
   ----------------------------------

   function Assume_Of_Subtype_Indication
     (Params : Translation_Params;
      N      : Node_Id) return W_Prog_Id is
   begin
      if Nkind (N) = N_Subtype_Indication then
         return
           Assume_of_Scalar_Subtype
             (Params, Etype (N), Etype (Subtype_Mark (N)));
      else
         return New_Void;
      end if;
   end Assume_Of_Subtype_Indication;

   ---------------------------
   -- Case_Expr_Of_Ada_Node --
   ---------------------------

   function Case_Expr_Of_Ada_Node
     (N             : Node_Id;
      Expected_Type : W_Base_Type_OId := Why_Empty;
      Domain        : EW_Domain;
      Params        : Translation_Params) return W_Expr_Id
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
               if Expected_Type = Why_Empty then
                  return
                    Transform_Expr
                       (Expression (N),
                        Domain,
                        Params);
               else
                  return
                    Transform_Expr
                       (Expression (N),
                        Expected_Type,
                        Domain,
                        Params);
               end if;

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
                                       Match_Domain,
                                       Params);

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
                       Transform_Discrete_Choice (Choice      => Cur_Choice,
                                                  Expr        => Matched_Expr,
                                                  Domain      => Cond_Domain,
                                                  Params      => Params),
                       Cond_Domain);
               Next (Cur_Choice);
            end loop;

            T :=
               New_Simpl_Conditional
                  (Condition => C,
                   Then_Part => Branch_Expr (Cur_Case),
                   Else_Part => T,
                   Domain    => Domain);
         end;
         Prev (Cur_Case);
      end loop;
      return T;
   end Case_Expr_Of_Ada_Node;

   -----------------------
   -- Compute_Call_Args --
   -----------------------

   function Compute_Call_Args
     (Call        : Node_Id;
      Domain      : EW_Domain;
      Nb_Of_Refs  : out Natural;
      Params      : Translation_Params) return W_Expr_Array
   is
      Subp   : constant Entity_Id := Entity (Name (Call));
      Assocs : constant List_Id := Parameter_Associations (Call);
      Len    : Nat;
      Read_Names : constant Name_Set.Set := Get_Reads (Subp);
   begin
      Nb_Of_Refs := 0;
      Len := List_Length (Assocs);

      if Domain = EW_Term then
         Len := Len + Int (Read_Names.Length);
      end if;

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

                  --  Parameters that are "out" are refs;
                  --  if the actual is a simple identifier and no conversion
                  --  is needed, it can be translated "as is".

                  if not Needs_Temporary_Ref (Actual, Formal) then
                     Why_Args (Cnt) := +Transform_Ident (Actual);

                  --  If a conversion or a component indexing is needed,
                  --  it can only be done for a value. That is to say,
                  --  something of this sort should be generated:
                  --
                  --  let formal = ref to_formal (!actual) in
                  --   (subprogram_call (formal); actual := !formal)
                  --
                  --  The generation of the context is left to the caller;
                  --  this function only signals the existence of such
                  --  parameters by incrementing Nb_Of_Refs.

                  else
                     Why_Args (Cnt) := +Transform_Ident (Formal);
                     Nb_Of_Refs := Nb_Of_Refs + 1;
                  end if;

               when others =>
                  --  No special treatment for parameters that are
                  --  not "out"
                  Why_Args (Cnt) :=
                    Transform_Expr (Actual,
                                    Type_Of_Node (Formal),
                                    Domain,
                                    Params);
            end case;
            Cnt := Cnt + 1;
         end Compute_Arg;

         procedure Iterate_Call is new
           Iterate_Call_Arguments (Compute_Arg);
      begin
         Iterate_Call (Call);

         if Domain = EW_Term then
            --  Workaround for K526-008 and K525-019

            for Elt of Read_Names loop
               if Params.Ref_Allowed then
                  Why_Args (Cnt) :=
                    New_Deref (Right => New_Identifier (Name => Elt.all));
               else
                  Why_Args (Cnt) := +New_Identifier (Name => Elt.all);
               end if;
               Cnt := Cnt + 1;
            end loop;
         end if;

         return Why_Args;
      end;
   end Compute_Call_Args;

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

      Index := New_Identifier (N, Full_Name (Defining_Identifier (Spec)));
   end Extract_From_Quantified_Expression;

   -------------------------------------
   -- Get_Pure_Logic_Term_If_Possible --
   -------------------------------------

   function Get_Pure_Logic_Term_If_Possible
     (Theory        : W_Theory_Declaration_Id;
      Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id) return W_Term_Id
   is
      Params : constant Translation_Params :=
                 (Theory      => Theory,
                  Phase       => Translation,
                  Ref_Allowed => True);
      Result : constant W_Term_Id :=
        +Transform_Expr (Expr, Expected_Type, EW_Term, Params);
   begin
      if Has_Dereference_Or_Any (Result) then
         return Why_Empty;
      else
         return Result;
      end if;
   end Get_Pure_Logic_Term_If_Possible;

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
               when Scalar_Kind =>
                  return Get_Range (Scalar_Range (N));

               when Object_Kind =>
                  return Get_Range (Scalar_Range (Etype (N)));

               when others =>
                  raise Program_Error;

            end case;

         when others =>
            raise Program_Error;
      end case;
   end Get_Range;

   ------------------------
   -- Insert_Ref_Context --
   ------------------------

   function Insert_Ref_Context
     (Params     : Translation_Params;
      Ada_Call   : Node_Id;
      Why_Call   : W_Prog_Id;
      Nb_Of_Refs : Positive)
     return W_Prog_Id
   is
      --  This goes recursively through the out/"in out" parameters
      --  to be converted; and collects, for each of them:
      --
      --  * the name of the corresponding tmp variable;
      --  * the expression of the conversion from the actual to the tmp;
      --  * a statement sequence for the conversions back to the actual.
      --
      --  The first two are set together after that. It cannot be done
      --  during the recursive traversal, as we are building its
      --  children during the traversal and that only root nodes can have
      --  their children modified.

      Ref_Context : W_Prog_Id;
      Index       : Positive := 1;
      Tmp_Vars    : W_Identifier_Array (1 .. Nb_Of_Refs);
      Fetch       : W_Prog_Array (1 .. Nb_Of_Refs);
      Store       : constant W_Statement_Sequence_Unchecked_Id :=
                      New_Unchecked_Statement_Sequence;

      procedure Process_Arg (Formal, Actual : Node_Id);

      -----------------
      -- Process_Arg --
      -----------------

      procedure Process_Arg (Formal, Actual : Node_Id) is
      begin
         if Needs_Temporary_Ref (Actual, Formal) then
            declare
               --  Types:

               Formal_T      : constant W_Base_Type_Id :=
                                 Type_Of_Node (Formal);
               Actual_T      : constant W_Base_Type_Id :=
                                 Type_Of_Node (Actual);

               --  Variables:

               Tmp_Var       : constant W_Identifier_Id :=
                                 Transform_Ident (Formal);
               Tmp_Var_Deref : constant W_Prog_Id :=
                                 New_Deref (Right => Tmp_Var);

               --  1/ Before the call (saving into a temporary variable):
               ----------------------------------------------------------

               --  On fetch, range checks are only needed when the formal
               --  is "in out". Disable them by using the term domain in
               --  case of "out" parameters.

               Fetch_Domain  : constant EW_Domain :=
                                 (if Ekind (Formal) in E_Out_Parameter then
                                    EW_Term
                                  else
                                    EW_Prog);

               --  Generate an expression of the form:
               --
               --    to_formal_type (from_actual_type (!actual))
               --
               --  ... with the appropriate range checks in the case of
               --  "in out" parameters:

               Fetch_Actual  : constant W_Prog_Id :=
                                 +Insert_Conversion
                                   (Domain   => Fetch_Domain,
                                    Ada_Node => Actual,
                                    Expr     =>
                                      +Transform_Expr (Actual,
                                                       EW_Prog,
                                                       Params),
                                    From     => Actual_T,
                                    To       => Formal_T);

               --  2/ After the call (storing the result):
               -------------------------------------------

               --  Generate an expression of the form:
               --
               --    to_actual_type_ (from_formal_type (!tmp_var))
               --
               --  ... with the appropriate range checks...

               Arg_Value     : constant W_Prog_Id :=
                                 +Insert_Conversion
                                   (Domain   => EW_Prog,
                                    Ada_Node => Actual,
                                    Expr     => +Tmp_Var_Deref,
                                    From     => Formal_T,
                                    To       => Actual_T);

               --  ...then store it into the actual:

               Store_Value   : constant W_Prog_Id :=
                                 New_Assignment
                                   (Ada_Node => Actual,
                                    Lvalue   => Actual,
                                    Expr     => Arg_Value);
            begin
               Statement_Sequence_Append_To_Statements (Store, Store_Value);
               Tmp_Vars (Index) := Tmp_Var;
               Fetch (Index) := Fetch_Actual;
               Index := Index + 1;
            end;
         end if;
      end Process_Arg;

      procedure Iterate_Call is new
        Iterate_Call_Arguments (Process_Arg);

   --  Start of processing for Insert_Ref_Context

   begin
      Statement_Sequence_Append_To_Statements (Store, Why_Call);
      Iterate_Call (Ada_Call);

      --  Set the pieces together

      Ref_Context := +Store;
      for J in Fetch'Range loop
         Ref_Context :=
           New_Binding_Ref
             (Name    => Tmp_Vars (J),
              Def     => Fetch (J),
              Context => Ref_Context);
      end loop;

      return Ref_Context;
   end Insert_Ref_Context;

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
         Cur_Formal := Next_Formal (Cur_Formal);

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

   -------------------------
   -- Needs_Temporary_Ref --
   -------------------------

   function Needs_Temporary_Ref
     (Actual : Node_Id;
      Formal : Node_Id)
     return Boolean is
   begin
      --  Temporary refs are needed for out or in out parameters that
      --  need a conversion or who are not an identifier.
      return Ekind (Formal) in E_In_Out_Parameter | E_Out_Parameter
        and then (not Eq (Etype (Actual), Etype (Formal))
                  or else not (Nkind (Actual) in N_Entity));
   end Needs_Temporary_Ref;

   --------------------
   -- New_Assignment --
   --------------------

   function New_Assignment
     (Ada_Node : Node_Id := Empty;
      Lvalue   : Node_Id;
      Expr     : W_Prog_Id) return W_Prog_Id
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

      function Why_Lvalue (N : Node_Id) return W_Identifier_Id;
      --  Compute the innermost that is accessed in the Lvalue, variable, ie
      --  the outermost data structure; this basically corresponds to "Prefix"
      --  above.

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
                        +Transform_Expr
                         (Prefix (N), EW_Prog, Params => Body_Params),
                        +Update_Expr,
                        EW_Prog,
                        Params => Body_Params));

            when others =>
               raise Not_Implemented;

         end case;
      end Compute_Rvalue;

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
            (Ada_Node => Ada_Node,
             Name     => W_Lvalue,
             Value    =>
               Compute_Rvalue (Lvalue, Expr));
   end New_Assignment;

   ----------------------
   -- One_Level_Access --
   ----------------------

   function One_Level_Access
     (N           : Node_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Translation_Params) return W_Expr_Id
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
               Ar      : constant Node_Id := Prefix (N);
               Dim     : constant Pos := Number_Dimensions (Type_Of_Node (Ar));
               T_Name  : constant String := Type_Of_Node (Ar);
               Indices : W_Expr_Array :=
                  (1 .. Integer (Dim) => <>);
               Cursor  : Node_Id := First (Expressions (N));
               Count   : Positive := 1;
            begin
               while Present (Cursor) loop
                  Indices (Count) :=
                     Transform_Expr
                        (Cursor, EW_Int_Type, Domain, Params);
                  Count := Count + 1;
                  Next (Cursor);
               end loop;

               return
                  New_Array_Access
                   (Ada_Node  => N,
                    Domain    => Domain,
                    Type_Name => T_Name,
                    Ar        => Expr,
                    Index     => Indices,
                    Dimension => Dim);
            end;

         when others =>
            raise Not_Implemented;

      end case;
   end One_Level_Access;

   ----------------------
   -- One_Level_Update --
   ----------------------

   function One_Level_Update
     (N           : Node_Id;
      Pref        : W_Expr_Id;
      Value       : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Translation_Params) return W_Expr_Id is
   begin
      case Nkind (N) is
         when N_Selected_Component =>
            return
              New_Record_Update (Name  => Pref,
                                 Field => Transform_Ident (Selector_Name (N)),
                                 Value => Value);

         when N_Indexed_Component =>
            declare
               Dim     : constant Pos :=
                  Number_Dimensions (Type_Of_Node (Prefix (N)));
               Indices : W_Expr_Array := (1 .. Integer (Dim) => <>);
               Cursor  : Node_Id := First (Expressions (N));
               Count   : Positive := 1;
            begin
               while Present (Cursor) loop
                  Indices (Count) :=
                     Transform_Expr
                        (Cursor, EW_Int_Type, EW_Prog, Params);
                  Count := Count + 1;
                  Next (Cursor);
               end loop;
               return
                  New_Array_Update (Ada_Node  => N,
                                    Type_Name => Type_Of_Node (Prefix (N)),
                                    Ar        => Pref,
                                    Index     => Indices,
                                    Value     => Value,
                                    Domain    => Domain,
                                    Dimension => Dim);
            end;

         when others =>
            raise Not_Implemented;

      end case;

   end One_Level_Update;

   ----------------
   -- Range_Expr --
   ----------------

   function Range_Expr
     (N           : Node_Id;
      T           : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Translation_Params;
      T_Type      : W_Base_Type_OId := Why_Empty) return W_Expr_Id
   is
      Subdomain  : constant EW_Domain :=
                     (if Domain = EW_Pred then EW_Term else Domain);
      Range_Node : constant Node_Id := Get_Range (N);
      Low        : constant Node_Id := Low_Bound (Range_Node);
      High       : constant Node_Id := High_Bound (Range_Node);
      Base_Type  : W_Base_Type_Id := Base_Why_Type (Low, High);
   begin
      if T_Type /= Why_Empty then
         Base_Type := Base_Why_Type (T_Type, Base_Type);
      end if;

      return
        New_Range_Expr
          (Domain    => Domain,
           Base_Type => Base_Type,
           Low       => +Transform_Expr (Low,
                                         Base_Type,
                                         Subdomain,
                                         Params),
           High      => +Transform_Expr (High,
                                         Base_Type,
                                         Subdomain,
                                         Params),
           Expr      => T);
   end Range_Expr;

   -------------------------------
   -- Transform_Array_Aggregate --
   -------------------------------

   procedure Transform_Array_Aggregate
     (Params : Translation_Params;
      Typ    : Entity_Id;
      Id     : W_Identifier_Id;
      Expr   : Node_Id)
   is
      use Why_Node_Sets;

      Func : constant W_Identifier_Id := New_Temp_Identifier;

      --  Predicate used to define the aggregate

      Params_No_Ref : constant Translation_Params :=
                        (Theory      => Params.Theory,
                         Phase       => Params.Phase,
                         Ref_Allowed => False);
      Pred : constant W_Pred_Id :=
               Transform_Array_Component_Associations
                 (Expr,
                  Typ,
                  Id,
                  Params_No_Ref);

      --  Compute the list of references used in the aggregate

      Params_Ref : constant Translation_Params :=
                     (Theory      => Params.Theory,
                      Phase       => Params.Phase,
                      Ref_Allowed => True);
      Pred_With_Refs : constant W_Pred_Id :=
                         Transform_Array_Component_Associations
                           (Expr,
                            Typ,
                            Id,
                            Params_Ref);
      Refs           : constant Why_Node_Sets.Set :=
                         Get_All_Dereferences (+Pred_With_Refs);

      --  Values used in calls to the aggregate function

      Ret_Type : constant W_Primitive_Type_Id :=
                   +Why_Logic_Type_Of_Ada_Type (Typ);
      Id_Binder : constant Binder_Type :=
                    (Ada_Node => Empty,
                     B_Name   => Id,
                     Modifier => None,
                     B_Type   => Ret_Type);
      Deref_Args : W_Expr_Array :=
                    (if Refs.Length = 0 then
                      (1 => New_Void)
                    else
                      (1 .. Integer (Refs.Length) => <>));
      Args : W_Expr_Array :=
                    (if Refs.Length = 0 then
                      (1 => New_Void)
                    else
                       (1 .. Integer (Refs.Length) => <>));
      Call, Deref_Call : W_Expr_Id;
      Id_Expr          : W_Expr_Id;
      Unique_Param     : constant Binder_Array :=
                   (if Refs.Length = 0 then
                      (1 => Unit_Param)
                    else
                      (1 .. 0 => <>));
      Other_Params   : Binder_Array :=
                   (if Refs.Length = 0 then
                      (1 .. 0 => <>)
                    else
                      (1 .. Integer (Refs.Length) => <>));
      Cnt      : Positive;
      Cursor   : Why_Node_Sets.Cursor;

   begin
      --  Compute the parameters/arguments for the function call and axiom

      Cnt := 1;
      Cursor := Refs.First;
      while Cursor /= No_Element loop
         Other_Params (Cnt) :=
           (Ada_Node => Empty,
            B_Name   => +Element (Cursor),
            Modifier => None,
            B_Type   =>
              New_Abstract_Type
                (Name => Object_Type_Name.Id
                     (Get_Name_String (Get_Symbol (+Element (Cursor))))));

         Args (Cnt) := +Element (Cursor);
         Deref_Args (Cnt) :=
           New_Deref (Right => +Element (Cursor));
         Next (Cursor);
         Cnt := Cnt + 1;
      end loop;

      --  Compute and store the translation of aggregate into Why terms, both
      --  w/ and w/o references allowed.

      Call := New_Call (Ada_Node => Empty,
                        Domain   => EW_Term,
                        Name     => Func,
                        Args     => Args);
      Deref_Call := New_Call (Ada_Node => Empty,
                              Domain   => EW_Term,
                              Name     => Func,
                              Args     => Deref_Args);

      Ada_To_Why_Term (True).Include (Expr, +Deref_Call);
      Ada_To_Why_Term (False).Include (Expr, +Call);

      --  Generate the necessary logic function and axiom declarations

      Emit
        (Params.Theory,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => Func,
            Binders     => Unique_Param & Other_Params,
            Return_Type => Ret_Type));

      Id_Expr := New_Comparison (Cmp       => EW_Eq,
                                 Left      => +Id,
                                 Right     => Call,
                                 Arg_Types => +Ret_Type,
                                 Domain    => EW_Pred);
      Emit
        (Params.Theory,
         New_Guarded_Axiom
           (Name        => Logic_Func_Axiom.Id (Func),
            Binders     => Binder_Array'(1 => Id_Binder) & Other_Params,
            Pre         => +Id_Expr,
            Def         => Pred));
   end Transform_Array_Aggregate;

   --------------------------------------------
   -- Transform_Array_Component_Associations --
   --------------------------------------------

   function Transform_Array_Component_Associations
     (Expr        : Node_Id;
      Typ         : Entity_Id;
      Id          : W_Identifier_Id;
      Params      : Translation_Params) return W_Pred_Id
   is
      T_Name  : constant String := Type_Of_Node (Typ);
      Num_Dim : constant Pos := Number_Dimensions (Typ);
      Indexes : W_Expr_Array (1 .. Positive (Num_Dim));
      Binders : W_Identifier_Array (1 .. Positive (Num_Dim));

      -----------------------
      -- Local subprograms --
      -----------------------

      function Constrain_Value_At_Index
        (Dim                 : Pos;
         Expr_Or_Association : Node_Id) return W_Expr_Id;
      --  Return the proposition that the array at the given indices is equal
      --  to the value given in Expr_Or_Association, or else "true" for box
      --  association.

      function Select_Nth_Index
        (Dim    : Pos;
         Offset : Nat) return W_Expr_Id;
      --  Return the proposition that Index is at Offset from Id'First

      function Select_These_Choices
        (Dim : Pos;
         L   : List_Id) return W_Expr_Id;
      --  Return a proposition that expresses that Index satisfies one choice
      --  in the list of choices L.

      function Transform_Rec_Aggregate
        (Dim  : Pos;
         Expr : Node_Id) return W_Expr_Id;
      --  Main recursive function operating over multi-dimensional array
      --  aggregates.

      ------------------------------
      -- Constrain_Value_At_Index --
      ------------------------------

      function Constrain_Value_At_Index
        (Dim                 : Pos;
         Expr_Or_Association : Node_Id) return W_Expr_Id
      is
         Expr : Node_Id;

      begin
         if Nkind (Expr_Or_Association) = N_Component_Association
           and then Box_Present (Expr_Or_Association)
         then
            return New_Literal (Value  => EW_True,
                                Domain => EW_Pred);
         else
            Expr :=
              (if Nkind (Expr_Or_Association) =
                 N_Component_Association
               then
                  Expression (Expr_Or_Association)
               else
                  Expr_Or_Association);

            if Dim < Num_Dim then
               pragma Assert (Nkind (Expr) = N_Aggregate);
               return Transform_Rec_Aggregate (Dim + 1, Expr);
            else
               declare
                  Exp_Type  : constant Node_Id := Component_Type (Typ);
                  Elmt_Type : constant W_Base_Type_Id :=
                                +Why_Logic_Type_Of_Ada_Type (Exp_Type);
                  Value     : constant W_Expr_Id :=
                                Transform_Expr (Expr          => Expr,
                                                Expected_Type => Elmt_Type,
                                                Domain        => EW_Term,
                                                Params        => Params);
                  Read      : constant W_Expr_Id :=
                                New_Array_Access
                                  (Ada_Node  => Expr_Or_Association,
                                   Domain    => EW_Term,
                                   Type_Name => T_Name,
                                   Ar        => +Id,
                                   Index     => Indexes,
                                   Dimension => Num_Dim);
               begin
                  return New_Comparison
                    (Cmp       => EW_Eq,
                     Left      => Read,
                     Right     => Value,
                     Arg_Types => Elmt_Type,
                     Domain    => EW_Pred);
               end;
            end if;
         end if;
      end Constrain_Value_At_Index;

      ----------------------
      -- Select_Nth_Index --
      ----------------------

      function Select_Nth_Index
        (Dim    : Pos;
         Offset : Nat) return W_Expr_Id
      is
         First : constant W_Expr_Id :=
                   New_Array_Attr
                     (Attribute_First,
                      T_Name,
                      +Id,
                      EW_Term,
                      Num_Dim,
                      UI_From_Int (Dim));
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
            Left      => Indexes (Integer (Dim)),
            Right     => Nth,
            Arg_Types => EW_Int_Type,
            Domain    => EW_Pred);
      end Select_Nth_Index;

      --------------------------
      -- Select_These_Choices --
      --------------------------

      function Select_These_Choices
        (Dim : Pos;
         L   : List_Id) return W_Expr_Id
      is
         Result : W_Expr_Id := New_Literal (Value  => EW_False,
                                            Domain => EW_Pred);
         Choice : Node_Id   := First (L);
      begin
         while Present (Choice) loop
            Result := New_Or_Expr
              (Left   => Result,
               Right  =>
                 Transform_Discrete_Choice
                   (Choice      => Choice,
                    Expr        => Indexes (Integer (Dim)),
                    Domain      => EW_Pred,
                    Params => Params),
               Domain => EW_Pred);
            Next (Choice);
         end loop;
         return Result;
      end Select_These_Choices;

      -----------------------------
      -- Transform_Rec_Aggregate --
      -----------------------------

      function Transform_Rec_Aggregate
        (Dim  : Pos;
         Expr : Node_Id) return W_Expr_Id
      is
         Exprs       : constant List_Id := Expressions (Expr);
         Assocs      : constant List_Id := Component_Associations (Expr);
         Association : Node_Id;
         Expression  : Node_Id;
         Else_Part   : W_Expr_Id := New_Literal (Value  => EW_True,
                                                 Domain => EW_Pred);
         Assocs_Len  : Nat;

      begin
         Assocs_Len := List_Length (Assocs);
         Association :=
           (if Nlists.Is_Empty_List (Assocs) then Empty
            else Nlists.Last (Assocs));

         --  Special case for "others" choice, which must appear alone as
         --  last association.

         if Present (Association)
           and then List_Length (Choices (Association)) = 1
           and then Nkind (First (Choices (Association))) = N_Others_Choice
         then
            if not Box_Present (Association) then
               Else_Part := Constrain_Value_At_Index (Dim, Association);
            end if;
            Prev (Association);
            Assocs_Len := Assocs_Len - 1;
         end if;

         Expression :=
           (if Nlists.Is_Empty_List (Exprs) then
               Empty
            else
               Nlists.Last (Exprs));

         if Present (Expression) then
            pragma Assert (No (Association));

            declare
               Elsif_Parts : W_Expr_Array
                 (1 .. Integer (List_Length (Exprs)) - 1);
            begin
               for Offset in reverse 1 .. List_Length (Exprs) - 1 loop
                  Elsif_Parts (Integer (Offset)) := New_Elsif
                    (Domain    => EW_Pred,
                     Condition => +Select_Nth_Index (Dim, Offset),
                     Then_Part => Constrain_Value_At_Index (Dim, Expression));
                  Prev (Expression);
               end loop;

               return New_Conditional
                 (Domain      => EW_Pred,
                  Condition   => +Select_Nth_Index (Dim, 0),
                  Then_Part   => Constrain_Value_At_Index (Dim, Expression),
                  Elsif_Parts => Elsif_Parts,
                  Else_Part   => Else_Part);
            end;

         elsif Present (Association) then
            declare
               Elsif_Parts : W_Expr_Array (1 .. Integer (Assocs_Len) - 1);
            begin
               for Offset in reverse 1 .. Assocs_Len - 1 loop
                  Elsif_Parts (Integer (Offset)) := New_Elsif
                    (Domain    => EW_Pred,
                     Condition =>
                       +Select_These_Choices (Dim, Choices (Association)),
                     Then_Part => Constrain_Value_At_Index (Dim, Association));
                  Prev (Association);
               end loop;

               return New_Conditional
                 (Domain      => EW_Pred,
                  Condition   =>
                    +Select_These_Choices (Dim, Choices (Association)),
                  Then_Part   => Constrain_Value_At_Index (Dim, Association),
                  Elsif_Parts => Elsif_Parts,
                  Else_Part   => Else_Part);
            end;

         else
            return Else_Part;
         end if;
      end Transform_Rec_Aggregate;

   --  Start of Transform_Array_Component_Associations

   begin
      for J in 1 .. Integer (Num_Dim) loop
         Binders (J) := New_Temp_Identifier;
         Indexes (J) := +Binders (J);
      end loop;

      return New_Universal_Quantif
        (Variables => Binders,
         Var_Type  => +EW_Int_Type,
         Pred      => +Transform_Rec_Aggregate (Dim => 1, Expr => Expr));
   end Transform_Array_Component_Associations;

   ------------------------------------
   -- Transform_Assignment_Statement --
   ------------------------------------

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id
   is
      function Expected_Type return W_Base_Type_Id;
      --  Compute the expected type of the right hand side expression.

      Lvalue   : constant Node_Id := Name (Stmt);
      --  The Lvalue in the Ada sense, ie the chain of accesses

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
               return Type_Of_Node
                 (Component_Type (Unique_Entity (Etype (Prefix (Lvalue)))));

            when N_Selected_Component =>
               return Type_Of_Node (Selector_Name (Lvalue));

            when others =>
               raise Not_Implemented;

         end case;
      end Expected_Type;

   --  Start of processing for Transform_Assignment_Statement

   begin
      return
        New_Assignment
          (Ada_Node => Stmt,
           Lvalue   => Lvalue,
           Expr     =>
             +Transform_Expr (Expression (Stmt),
                              Expected_Type,
                              EW_Prog,
                              Params => Body_Params));
   end Transform_Assignment_Statement;

   --------------------
   -- Transform_Attr --
   --------------------

   function Transform_Attr
     (Expr          : Node_Id;
      Domain        : EW_Domain;
      Current_Type  : out W_Base_Type_Id;
      Params        : Translation_Params) return W_Expr_Id
   is
      Aname   : constant Name_Id := Attribute_Name (Expr);
      Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
      Var     : constant Node_Id      := Prefix (Expr);
      T       : W_Expr_Id;
   begin
      Current_Type := Type_Of_Node (Expr);
      case Attr_Id is
         when Attribute_Result =>
            if Params.Phase in Generate_VCs then
               T :=
                 New_Deref
                   (Ada_Node => Expr,
                    Right    => Name_For_Result);
            else
               T := +New_Result_Term;
            end if;

         when Attribute_Old =>
            if Params.Phase = Generate_VCs_For_Post then
               T := +Name_For_Old (Var);
            else
               T :=
                 New_Tagged (Def    => Transform_Expr
                             (Var, Domain, Params),
                             Tag    => NID (""),
                             Domain => Domain);
            end if;

         when Attribute_Pred | Attribute_Succ =>
            declare
               Op     : constant EW_Binary_Op :=
                          (if Attr_Id = Attribute_Succ then
                             EW_Add
                           else
                             EW_Substract);
               Old    : W_Expr_Id;
               Offset : W_Expr_Id;
               A_Type : constant Entity_Id := Etype (Var);
               W_Type : EW_Scalar;
            begin
               case Ekind (Etype (Var)) is
                  when Discrete_Kind =>
                     if A_Type = Standard_Boolean then
                        W_Type := EW_Bool;
                        raise Not_Implemented;
                     else
                        W_Type := EW_Int;
                        Offset := New_Integer_Constant (Value => Uint_1);
                     end if;

                  when Float_Kind =>
                     W_Type := EW_Real;

                     --  ??? This is not strictly correct; F'Succ (A) is
                     --  usually different from A + F'Succ (0.0). But the
                     --  correct computation will be much more complicated;
                     --  and, as we map floating points to reals, our model
                     --  is quite loose anyway.

                     Offset :=
                       New_Real_Constant
                         (Value =>
                            Eval_Fat.Succ
                              (Root_Type (A_Type),
                               Ureal_0));

                  when Fixed_Point_Kind =>
                     W_Type := EW_Real;
                     Offset :=
                       New_Real_Constant (Value => Small_Value (A_Type));

                  when others =>
                     --  All possible cases should have been handled
                     --  before this point.
                     pragma Assert (False);
                     null;
               end case;

               Old :=
                 Transform_Expr
                   (First (Expressions (Expr)),
                    Why_Types (W_Type),
                    Domain,
                    Params);

               T :=
                 New_Binary_Op
                   (Ada_Node => Expr,
                    Left     => Old,
                    Right    => Offset,
                    Op       => Op,
                    Op_Type  => W_Type);
               Current_Type := Why_Types (W_Type);
            end;

         when Attribute_Pos =>
            T := Transform_Expr (First (Expressions (Expr)),
                                 EW_Int_Type,
                                 Domain,
                                 Params);
            Current_Type := EW_Int_Type;

         when Attribute_Val =>
            declare
               Val_Type : constant W_Base_Type_Id := Type_Of_Node (Var);
            begin
               T := Transform_Expr (First (Expressions (Expr)),
                                    Val_Type,
                                    Domain,
                                    Params);
               Current_Type := Val_Type;
            end;

         when Attribute_First | Attribute_Last | Attribute_Length =>
            case Ekind (Etype (Var)) is
               when Array_Kind =>

                  --  Array_Type'First

                  if Nkind (Var) = N_Identifier and then
                    Is_Type (Entity (Var)) then

                     T := New_Attribute_Expr
                       (Etype (First_Index (Entity (Var))),
                        Attr_Id);
                  else
                     T :=
                       New_Array_Attr
                         (Attr_Id,
                          Full_Name (Etype (Var)),
                          Transform_Expr (Var, Domain, Params),
                          Domain,
                          Number_Dimensions (Type_Of_Node (Var)),
                          (if Present (Expressions (Expr)) then
                             Expr_Value (First (Expressions (Expr)))
                           else Uint_1));
                  end if;
                  Current_Type := EW_Int_Type;

               when Discrete_Kind | Real_Kind =>
                  T := New_Attribute_Expr (Etype (Var), Attr_Id);
                  Current_Type :=
                    (if Ekind (Etype (Var)) in Discrete_Kind
                     then EW_Int_Type else EW_Real_Type);

               when others =>
                  --  All possible cases should have been handled
                  --  before this point.
                  pragma Assert (False);
                  null;
            end case;

         when Attribute_Modulus =>
            T := New_Attribute_Expr (Etype (Var), Attr_Id);
            Current_Type := EW_Int_Type;

         when Attribute_Mod =>
            T :=
              New_Call (Ada_Node => Expr,
                        Domain   => Domain,
                        Name     => New_Integer_Mod.Id,
                        Args     =>
                          (1 => Transform_Expr (First (Expressions (Expr)),
                                                EW_Int_Type,
                                                Domain,
                                                Params),
                           2 =>
                           New_Attribute_Expr
                              (Etype (Var), Attribute_Modulus)));
            Current_Type := EW_Int_Type;

         when others =>
            raise Not_Implemented;
      end case;
      return T;
   end Transform_Attr;

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
         when N_Op_Concat | N_Op_Expon => raise Program_Error;
         when others => raise Program_Error;
      end case;
   end Transform_Binop;

   -------------------------------
   -- Transform_Block_Statement --
   -------------------------------

   function Transform_Block_Statement (N : Node_Id) return W_Prog_Id
   is
      Core : constant W_Prog_Id :=
         Transform_Statements (Statements (Handled_Statement_Sequence (N)));
   begin
      if Present (Declarations (N)) then
         return Transform_Declarations_Block (Declarations (N), Core);
      else
         return Core;
      end if;
   end Transform_Block_Statement;

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

   ----------------------------------
   -- Transform_Declarations_Block --
   ----------------------------------

   function Transform_Declarations_Block (L : List_Id; Core : W_Prog_Id)
      return W_Prog_Id
   is
      procedure Assume_of_Scalar_Subtype
        (Params : Translation_Params;
         Ent    : Entity_Id;
         Base   : Entity_Id;
         R      : in out W_Prog_Id);
      --  Local Wrapper for Assume_of_Scalar_Subtype

      function Get_Base_Type (N : Node_Id) return Entity_Id;
      --  Return the base type when N is the node of a (sub-)type
      --  declaration which requires a check.
      --  Return Empty otherwise.

      ------------------------------
      -- Assume_of_Scalar_Subtype --
      ------------------------------

      procedure Assume_of_Scalar_Subtype
        (Params : Translation_Params;
         Ent    : Entity_Id;
         Base   : Entity_Id;
         R      : in out W_Prog_Id)
      is
      begin

         --  If the range is not static, we need to generate a check that
         --  the subtype declaration is valid; otherwise, the frontend has
         --  done it for us already

         if not Is_Static_Range (Get_Range (Ent)) then
            R := Sequence (Assume_of_Scalar_Subtype (Params, Ent, Base), R);
         end if;
      end Assume_of_Scalar_Subtype;

      -------------------
      -- Get_Base_Type --
      -------------------

      function Get_Base_Type (N : Node_Id) return Entity_Id
      is
         Ent : constant Entity_Id := Defining_Identifier (N);
      begin

         --  Full type declarations can only require checks when they are
         --  scalar types, and then only when the range is non-static.
         if Nkind (N) = N_Full_Type_Declaration then
            if Ekind (Ent) in Scalar_Kind then
               if Is_Static_Range (Get_Range (Ent)) then
                  return Empty;
               end if;
            end if;
            declare
               T_Def : constant Node_Id := Type_Definition (N);
            begin
               case Nkind (T_Def) is
                  when N_Subtype_Indication =>
                     return Entity (Subtype_Mark (T_Def));

                  when N_Derived_Type_Definition =>
                     declare
                        S : constant Node_Id := Subtype_Indication (T_Def);
                     begin
                        if Nkind (S) = N_Subtype_Indication then
                           return Entity (Subtype_Mark (S));
                        else
                           return Entity (S);
                        end if;
                     end;

                  when others =>
                     return Empty;

               end case;
            end;
         else
            declare
               S : constant Node_Id := Subtype_Indication (N);
            begin
               if Nkind (S) = N_Subtype_Indication then
                  return Entity (Subtype_Mark (S));
               else
                  return Entity (S);
               end if;
            end;
         end if;
      end Get_Base_Type;

      Cur_Decl : Node_Id := Last (L);
      R        : W_Prog_Id := Core;
   begin
      while Present (Cur_Decl) loop
         case Nkind (Cur_Decl) is
            when N_Object_Declaration =>
               R := Sequence (Assignment_of_Obj_Decl (Cur_Decl), R);

            when N_Subtype_Declaration | N_Full_Type_Declaration =>
               declare
                  Ent : constant Entity_Id :=
                     Defining_Identifier (Cur_Decl);
                  Base : constant Entity_Id := Get_Base_Type (Cur_Decl);
               begin
                  if Present (Base) then
                     case Ekind (Ent) is
                        when Scalar_Kind =>
                           Assume_of_Scalar_Subtype
                             (Body_Params, Ent, Base, R);

                        when Array_Kind =>
                           declare
                              Index      : Node_Id := First_Index (Ent);
                              Index_Base : Entity_Id := First_Index (Base);
                           begin
                              while Present (Index) loop
                                 Assume_of_Scalar_Subtype
                                   (Body_Params,
                                    Etype (Index),
                                    Etype (Index_Base),
                                    R);
                                 Next (Index);
                                 Next (Index_Base);
                              end loop;
                           end;

                        when E_Record_Type =>
                           null;

                        when others =>
                           raise Not_Implemented;

                     end case;
                  end if;
               end;

            when others =>
               null;

         end case;
         Prev (Cur_Decl);
      end loop;
      return R;
   end Transform_Declarations_Block;

   -------------------------------
   -- Transform_Discrete_Choice --
   -------------------------------

   function Transform_Discrete_Choice
     (Choice      : Node_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Translation_Params) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
      Is_Range  : Boolean;

   begin
      if Nkind (Choice) = N_Others_Choice then
         return New_Literal (Domain => Domain, Value => EW_True);
      end if;

      case Nkind (Choice) is
         when N_Subtype_Indication | N_Range =>
            Is_Range := True;
         when N_Identifier | N_Expanded_Name =>
            if Ekind (Entity (Choice)) in Type_Kind then
               Is_Range := True;
            else
               Is_Range := False;
            end if;
         when N_Others_Choice =>
            raise Program_Error;
         when others =>
            Is_Range := False;
      end case;

      if Is_Range then
         return Range_Expr (Choice, Expr, Domain, Params);
      else
         return New_Comparison
           (Cmp       => EW_Eq,
            Left      => Expr,
            Right     => Transform_Expr (Expr          => Choice,
                                         Expected_Type => EW_Int_Type,
                                         Domain        => Subdomain,
                                         Params        => Params),
            Arg_Types => EW_Int_Type,
            Domain    => Domain);
      end if;
   end Transform_Discrete_Choice;

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

      Current_Type := EW_Int_Type;
      return New_Integer_Constant
               (Ada_Node => Enum,
                Value    => Enumeration_Pos (Entity (Enum)));
   end Transform_Enum_Literal;

   --------------------
   -- Transform_Expr --
   --------------------

   function Transform_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id;
      Domain        : EW_Domain;
      Params        : Translation_Params) return W_Expr_Id
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
              Left     =>
              +Transform_Expr (Expr, EW_Bool_Type, EW_Term, Params),
              Right    => New_Literal (Value => EW_True, Domain => EW_Prog),
              Op       => EW_Eq);
      end if;

      case Nkind (Expr) is
         when N_Aggregate =>
            declare
               Expr_Type : constant Entity_Id := Type_Of_Node (Expr);
            begin
               if Is_Record_Type (Expr_Type) then
                  pragma Assert (No (Expressions (Expr)));
                  T :=
                     New_Record_Aggregate
                       (Associations => Transform_Record_Component_Associations
                                          (Domain,
                                           Expr_Type,
                                           Component_Associations (Expr),
                                           Params));
                  Current_Type := EW_Abstract (Expr_Type);
               else
                  pragma Assert
                     (Is_Array_Type (Expr_Type) or else
                      Is_String_Type (Expr_Type));
                  declare
                     Id : constant W_Identifier_Id :=
                            (if Domain = EW_Term then
                               New_Temp_Identifier
                             else New_Result_Identifier.Id);
                     BT : constant W_Base_Type_Id :=
                                   +Why_Logic_Type_Of_Ada_Type (Expr_Type);
                  begin
                     if Domain = EW_Term then
                        if not (Ada_To_Why_Term (Params.Ref_Allowed).
                                   Contains (Expr)) then
                           Transform_Array_Aggregate
                             (Params, Expr_Type, Id, Expr);
                        end if;
                        T := +Ada_To_Why_Term (Params.Ref_Allowed).
                          Element (Expr);
                     else
                        T := New_Simpl_Any_Expr
                          (Domain   => Domain,
                           Arg_Type => +BT,
                           Id       => Id,
                           Pred     =>
                             Transform_Array_Component_Associations
                               (Expr,
                                Expr_Type,
                                Id,
                                Params));
                     end if;
                     Current_Type := EW_Abstract (Expr_Type);
                  end;
               end if;
            end;

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
            --  even between two litterals. Note that Alfa-marking makes sure
            --  the original node is in Alfa in this case.

            if Is_Rewrite_Substitution (Expr) then
               T := Transform_Expr (Original_Node (Expr),
                                    EW_Real_Type,
                                    Domain,
                                    Params);

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

         when N_String_Literal =>
            if not (Ada_To_Why_Term (Params.Ref_Allowed).Contains (Expr)) then
               Transform_String_Literal (Params, Expr);
            end if;
            T := +Ada_To_Why_Term (Params.Ref_Allowed).Element (Expr);

         when N_Identifier | N_Expanded_Name =>
            declare
               Id : constant W_Identifier_Id := Transform_Ident (Expr);
            begin
               case Ekind (Entity (Expr)) is
                  --  First treat special cases

                  when E_Enumeration_Literal =>
                     T := Transform_Enum_Literal (Expr, Current_Type, Domain);

                  when others =>
                     if Is_Mutable (Entity (Expr))
                       and then Params.Ref_Allowed
                     then
                        T :=
                          New_Deref
                            (Ada_Node => Expr,
                             Right    => Id);
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
                             Transform_Expr (Left, BT, Subdomain,
                                             Params);
               Right_Arg : constant W_Expr_Id :=
                             Transform_Expr (Right, BT, Subdomain,
                                             Params);
            begin
               if Is_Array_Type (Etype (Left)) then
                  T := New_Call (Ada_Node => Expr,
                                 Domain   => Subdomain,
                                 Name     =>
                                   Array_Equal_Name.Id
                                    (New_Ada_Array_Name
                                    (Number_Dimensions (Type_Of_Node (Left)))),
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
                    Op       => EW_Minus,
                    Right    =>
                    +Transform_Expr (Right, Current_Type, Domain,
                     Params),
                    Op_Type  => Get_Base_Type (Current_Type));
               T := Apply_Modulus
                      (Etype (Expr),
                       T,
                       Domain,
                       Overflow_Check_Needed);
            end;

         when N_Op_Plus =>
            --  unary plus
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Right);
               T := Transform_Expr (Right, Current_Type, Domain, Params);
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
                      (1 => Transform_Expr (Right, Current_Type,
                       Domain, Params)));
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
                                                Domain,
                                                Params),
                    Right    => Transform_Expr (Right,
                                                Current_Type,
                                                Domain,
                                                Params),
                    Op       => Transform_Binop (Nkind (Expr)),
                    Op_Type  => Get_Base_Type (Current_Type));
               T := Apply_Modulus
                      (Etype (Expr),
                       T,
                       Domain,
                       Overflow_Check_Needed);
            end;

         when N_Op_Divide =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Name  : W_Identifier_Id;
            begin
               Current_Type := Base_Why_Type (Left, Right);
               Name := New_Division (Get_Base_Type (Current_Type));
               if Domain = EW_Prog then
                  Name := To_Program_Space (Name);
               end if;

               T :=
                 New_Located_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => Name,
                    Progs    =>
                      (1 => Transform_Expr (Left,
                                            Current_Type,
                                            Domain,
                                            Params),
                       2 => Transform_Expr (Right,
                                            Current_Type,
                                            Domain,
                                            Params)),
                    Reason   => VC_Division_Check);
               T := Apply_Modulus
                      (Etype (Expr),
                       T,
                       Domain,
                       Overflow_Check_Needed);
            end;

         when N_Op_Rem | N_Op_Mod =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Name  : W_Identifier_Id;
            begin
               Current_Type := Base_Why_Type (Left, Right);
               Name := (if Nkind (Expr) = N_Op_Rem then
                          New_Integer_Rem.Id
                        else
                          New_Integer_Mod.Id);
               Name := (if Domain = EW_Prog then
                          To_Program_Space (Name)
                        else
                          Name);
               T :=
                 New_Located_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => Name,
                    Progs    =>
                      (1 => Transform_Expr (Left,
                                            Current_Type,
                                            Domain,
                                            Params),
                       2 => Transform_Expr (Right,
                                            Current_Type,
                                            Domain,
                                            Params)),
                    Reason   => VC_Division_Check);
            end;

         when N_Op_Not =>
            Current_Type := EW_Bool_Type;
            if Domain = EW_Term then
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => New_Identifier (Name => "notb"),
                    Args     =>
                      (1 => Transform_Expr (Right_Opnd (Expr),
                                            EW_Bool_Type,
                                            Domain,
                                            Params)));
            else
               T :=
                 New_Not
                   (Right  => Transform_Expr (Right_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Params),
                    Domain => Domain);
            end if;

         when N_Op_And =>
            T :=
               New_And_Expr
                 (Left   => Transform_Expr (Left_Opnd (Expr),
                                            EW_Bool_Type,
                                            Domain,
                                            Params),
                  Right  => Transform_Expr (Right_Opnd (Expr),
                                            EW_Bool_Type,
                                            Domain,
                                            Params),
                  Domain => Domain);
            Current_Type := EW_Bool_Type;

         when N_Op_Or =>
            T :=
               New_Or_Expr
                 (Left     => Transform_Expr (Left_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Params),
                  Right    => Transform_Expr (Right_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Params),
                  Domain   => Domain);
            Current_Type := EW_Bool_Type;

         when N_Op_Xor =>
            T :=
               New_Xor_Expr
                 (Left     => Transform_Expr (Left_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Params),
                  Right    => Transform_Expr (Right_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Params),
                  Domain   => Domain);
            Current_Type := EW_Bool_Type;

         when N_And_Then =>
            T :=
               New_And_Then_Expr
                 (Left   => Transform_Expr (Left_Opnd (Expr),
                                            Current_Type,
                                            Domain,
                                            Params),
                  Right  => Transform_Expr (Right_Opnd (Expr),
                                            Current_Type,
                                            Domain,
                                            Params),
                  Domain => Domain);
            Current_Type := EW_Bool_Type;

         when N_Or_Else =>
            T :=
               New_Or_Else_Expr
                 (Left   => Transform_Expr (Left_Opnd (Expr),
                                            Current_Type,
                                            Domain,
                                            Params),
                  Right  => Transform_Expr (Right_Opnd (Expr),
                                            Current_Type,
                                            Domain,
                                            Params),
                  Domain => Domain);
            Current_Type := EW_Bool_Type;

         when N_In =>
            declare
               Subdomain : constant EW_Domain :=
                             (if Domain = EW_Pred then EW_Term else Domain);
               Var       : constant Node_Id := Left_Opnd (Expr);
            begin
               T :=
                 Range_Expr
                   (Right_Opnd (Expr),
                    Transform_Expr (Var,
                                    Base_Why_Type (Var),
                                    Subdomain,
                                    Params),
                    Domain,
                    Params);
            end;

         when N_Quantified_Expression =>
            T := Transform_Quantified_Expression
              (Expr, Domain, Params, Current_Type);

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
                                                    Cond_Domain,
                                                    Params),
                      Then_Part => Transform_Expr (Then_Part,
                                                   Current_Type,
                                                   Domain,
                                                   Params),
                      Else_Part => Transform_Expr (Else_Part,
                                                   Current_Type,
                                                   Domain,
                                                   Params));
            end;

         when N_Type_Conversion =>
            return Transform_Expr (Expression (Expr),
                                   Expected_Type,
                                   Domain,
                                   Params);

         when N_Unchecked_Type_Conversion =>
            --  Compiler inserted conversions are trusted
            pragma Assert (not Comes_From_Source (Expr));
            return Transform_Expr (Expression (Expr),
                                   Expected_Type,
                                   Domain,
                                   Params);

         when N_Function_Call =>
            declare
               Ident      : constant W_Identifier_Id :=
                              Transform_Ident (Name (Expr));

               --  Retrieve type of function result from function called

               Result_Typ : constant Entity_Id :=
                              Unique_Entity
                                (Entity (Result_Definition
                                   (Parent (Entity (Name (Expr))))));
               Name       : constant W_Identifier_Id :=
                              (if Domain = EW_Prog then
                                 To_Program_Space (Ident)
                              else
                                 Logic_Func_Name.Id (Ident));
               Nb_Of_Refs : Natural;
            begin
               Current_Type := +Why_Logic_Type_Of_Ada_Type (Result_Typ);
               T :=
                 +New_Located_Call
                   (Name     => Name,
                    Progs    => Compute_Call_Args (Expr,
                                                   Domain,
                                                   Nb_Of_Refs,
                                                   Params),
                    Ada_Node => Expr,
                    Domain   => Domain,
                    Reason   => VC_Precondition);

               pragma Assert (Nb_Of_Refs = 0,
                              "Only pure functions are in alfa");
            end;

         when N_Indexed_Component | N_Selected_Component =>
            T := One_Level_Access (Expr,
                                   Transform_Expr
                                     (Prefix (Expr), Domain, Params),
                                   Domain,
                                   Params);

         when N_Attribute_Reference =>
            T := Transform_Attr (Expr,
                                 Domain,
                                 Current_Type,
                                 Params);

         when N_Case_Expression =>
            T := Case_Expr_Of_Ada_Node
                   (Expr,
                    Expected_Type,
                    Domain,
                    Params);
            Current_Type := Expected_Type;

         when N_Expression_With_Actions =>
            if not (Domain = EW_Prog) then
               raise Not_Implemented;
            end if;

            T :=
               +Sequence
                 (Transform_Statements (Actions (Expr)),
                  +Transform_Expr (Expression (Expr),
                                   Expected_Type,
                                   EW_Prog,
                                   Params));

         when N_Qualified_Expression =>
            Current_Type := Base_Why_Type (Expression (Expr));
            T := Transform_Expr (Expression (Expr),
                                 Current_Type,
                                 Domain,
                                 Params);

         when others =>
            raise Not_Implemented;

      end case;

      declare
         By    : constant W_Base_Type_Id :=
                   (if Overflow_Check_Needed then
                      EW_Abstract (Etype (Expr))
                    else
                      Why_Empty);
      begin
         case Domain is
            when EW_Term | EW_Prog =>
               return
                 Insert_Conversion
                   (Domain   => Domain,
                    Ada_Node => Expr,
                    Expr     => T,
                    From     => Current_Type,
                    To       => Expected_Type,
                    By       => By);

            when EW_Pred =>
               return T;

         end case;
      end;
   end Transform_Expr;

   function Transform_Expr
     (Expr        : Node_Id;
      Domain      : EW_Domain;
      Params      : Translation_Params) return W_Expr_Id is
   begin
      return Transform_Expr (Expr, Type_Of_Node (Expr), Domain, Params);
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

      return New_Identifier (Id, Full_Name (Ent));
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
         Runtime := New_Ignore
           (Prog => +Transform_Expr (Expr, EW_Prog, Params => Body_Params));
         return +Transform_Expr (Expr, EW_Pred, Params => Body_Params);
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
      Params       : Translation_Params;
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
                                            EW_Pred, Params);
            Hypothesis : W_Pred_Id;
            Quant_Body : W_Pred_Id;
         begin
            Hypothesis := +Range_Expr (Range_E, +Index, EW_Pred, Params);
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
         --    [ { } bool { result = true <-> expr } ]
         --  The condition is a formula that expresses that i is in the
         --  range given by the quantification.
         declare
            Why_Expr   : constant W_Prog_Id :=
                           New_Ignore
                             (Prog =>
                                +Transform_Expr (Condition (Expr),
                                                 EW_Prog, Params));
            Range_Cond : W_Prog_Id;
         begin
            Range_Cond := +Range_Expr (Range_E, +Index, EW_Prog, Params);
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
                      +W_Expr_Id'(New_Connection
                        (Domain   => EW_Pred,
                         Left     =>
                           New_Relation
                             (Domain   => EW_Pred,
                              Op_Type  => EW_Bool,
                              Left     => +New_Result_Identifier.Id,
                              Op       => EW_Eq,
                              Right    => New_Literal (Value  => EW_True,
                                                       Domain => EW_Term)),
                         Op       => EW_Equivalent,
                         Right    =>
                           +Transform_Expr (Expr, EW_Pred, Params)))));
         end;
      else
         raise Not_Implemented;
      end if;
   end Transform_Quantified_Expression;

   ---------------------------------------------
   -- Transform_Record_Component_Associations --
   ---------------------------------------------

   function Transform_Record_Component_Associations
     (Domain      : EW_Domain;
      Typ         : Entity_Id;
      Assocs      : List_Id;
      Params      : Translation_Params) return W_Field_Association_Array
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
                  Expr := Transform_Expr
                    (Expression (Association),
                     +Why_Logic_Type_Of_Ada_Type (Etype (Component)),
                     Domain, Params);
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
                   Field  => New_Identifier (Typ, Full_Name (Component)),
                   Value  => Expr);
            J := J + 1;
            Component := Next_Component (Component);
         end;
      end loop;
      pragma Assert (No (Association));
      return Result;
   end Transform_Record_Component_Associations;

   -------------------------
   -- Transform_Statement --
   -------------------------

   function Transform_Statement (Stmt : Node_Id) return W_Prog_Id is
   begin
      case Nkind (Stmt) is
         when N_Label | N_Null_Statement =>
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
                          Name     => Name_For_Result,
                          Value    =>
                            +Transform_Expr (Expression (Stmt),
                                             Return_Type,
                                             EW_Prog,
                                             Params => Body_Params));
                     return Sequence (Result_Stmt, Raise_Stmt);
                  end;
               else
                  return Raise_Stmt;
               end if;
            end;

         when N_Procedure_Call_Statement =>
            declare
               Nb_Of_Refs : Natural;
               Call       : constant W_Prog_Id :=
                              +New_Located_Call
                                (Ada_Node => Stmt,
                                 Name     =>
                                   To_Program_Space
                                     (Transform_Ident (Name (Stmt))),
                                 Progs    =>
                                   Compute_Call_Args
                                     (Stmt, EW_Prog, Nb_Of_Refs,
                                      Params => Body_Params),
                                 Domain   => EW_Prog,
                                 Reason   => VC_Precondition);
            begin
               if Nb_Of_Refs = 0 then
                  return Call;
               else
                  return
                    Insert_Ref_Context (Body_Params, Stmt, Call, Nb_Of_Refs);
               end if;
            end;

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
                               Transform_Expr
                                 (Condition (Cur),
                                  EW_Bool_Type,
                                  EW_Prog,
                                  Params => Body_Params),
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
                                               EW_Bool_Type,
                                               EW_Prog,
                                               Params => Body_Params),
                    Then_Part =>
                      +Transform_Statements (Then_Statements (Stmt)),
                    Else_Part => +Tail,
                    Domain    => EW_Prog);
            end;

         when N_Raise_xxx_Error =>
            raise Not_Implemented;

         when N_Object_Declaration =>
            return Assignment_of_Obj_Decl (Stmt);

         when N_Object_Renaming_Declaration =>

            --  Renamings are replaced by the renamed object in the frontend,
            --  but the renaming objects are not removed from the tree. We can
            --  safely ignore them.

            return New_Void;

         when N_Loop_Statement =>
            return Transform_Loop_Statement (Stmt);

         when N_Exit_Statement =>
            return Transform_Exit_Statement (Stmt);

         when N_Case_Statement =>
            return
              +Case_Expr_Of_Ada_Node
                 (N           => Stmt,
                  Domain      => EW_Prog,
                  Params      => Body_Params);

         when N_Block_Statement =>
            return Transform_Block_Statement (Stmt);

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
                             Expr     => +New_Identifier (Name => "absurd"),
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

   procedure Transform_String_Literal
     (Params : Translation_Params;
      N      : Node_Id)
   is
      Id       : constant W_Identifier_Id := New_Temp_Identifier;
      Ty       : constant Entity_Id := Type_Of_Node (N);
      Why_Type : constant W_Primitive_Type_Id :=
         +Why_Logic_Type_Of_Ada_Type (Ty);
   begin
      Emit
        (Params.Theory,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => Id,
            Binders     => (1 .. 0 => <>),
            Return_Type => Why_Type));

      Ada_To_Why_Term (True).Include (N, +Id);
      Ada_To_Why_Term (False).Include (N, +Id);
   end Transform_String_Literal;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return Entity_Id is
   begin
      if Nkind (N) in N_Entity then
         if Ekind (N) in Type_Kind then
            return N;
         else
            return Unique_Entity (Etype (N));
         end if;
      elsif Nkind (N) in N_Identifier | N_Expanded_Name then
         return Unique_Entity (Etype (Entity (N)));
      else
         return Unique_Entity (Etype (N));
      end if;
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return String
   is
      E : constant Entity_Id := Type_Of_Node (N);
   begin
      if E = Standard_Boolean then
         return Why_Scalar_Type_Name (EW_Bool);
      elsif E = Universal_Fixed then
         return Why_Scalar_Type_Name (EW_Real);
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
      elsif E = Universal_Fixed then
         return EW_Real_Type;
      else
         return EW_Abstract (E);
      end if;
   end Type_Of_Node;

end Gnat2Why.Expr;
