------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - E X P R                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2023, AdaCore                     --
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

with Checked_Types;              use Checked_Types;
with Common_Containers;          use Common_Containers;
with Flow_Types;                 use Flow_Types;
with Gnat2Why.Util;              use Gnat2Why.Util;
with SPARK_Atree;                use SPARK_Atree;
with SPARK_Atree.Entities;       use SPARK_Atree.Entities;
with SPARK_Util;                 use SPARK_Util;
with SPARK_Util.Types;           use SPARK_Util.Types;
with Types;                      use Types;
with Why.Conversions;            use Why.Conversions;
with Why.Gen.Expr;               use Why.Gen.Expr;
with Why.Gen.Terms;              use Why.Gen.Terms;
with Why.Ids;                    use Why.Ids;
with Why.Inter;                  use Why.Inter;
with Why.Sinfo;                  use Why.Sinfo;
with Why.Types;                  use Why.Types;

package Gnat2Why.Expr is

   procedure Assume_Declaration_Of_Entity
     (E             :        Extended_Object_Kind_Id;
      Params        :        Transformation_Params;
      Initialized   :        Boolean;
      Top_Predicate :        Boolean;
      Context       : in out W_Prog_Id);
   --  Add to Context assumption for a declared entity. They include both its
   --  dynamic invariant and its value if it is a constant whose value contains
   --  no dereference.
   --  @param E Entity of the object that we want to declare
   --  @param Params Transformation parameters to be used
   --  @param Initialized True iff E is known to be initialized
   --  @param Top_Predicate True iff the dynamic invariant should consider
   --     the toplevel type predicate possibly associated with [Ty].
   --  @param Context The Why program to which we want to append the
   --     assumptions.

   function Assume_Dynamic_Invariant
     (Expr          : W_Term_Id;
      Ty            : Type_Kind_Id;
      Initialized   : Boolean := True;
      Only_Var      : Boolean := True;
      Top_Predicate : Boolean := True)
      return W_Prog_Id;
   --  @param Expr Why3 expression on which to assume the dynamic invariant
   --  @param Ty type of expression [Expr]
   --  @param Initialized True iff Expr is known to be initialized
   --  @param Only_Var True iff the dynamic invariant should only consider
   --     the variable parts of [Expr].
   --  @param Top_Predicate True iff the dynamic invariant should consider
   --     the toplevel type predicate possibly associated with [Ty].
      --  @result Why3 program assuming the dynamic invariant of type [Ty]
   --     over [Expr].

   function Assume_Dynamic_Invariant_For_Variables
     (Vars             : Node_Sets.Set;
      Params           : Transformation_Params;
      Scope            : Entity_Id := Empty;
      Exclude_Top_Pred : Entity_Id := Empty;
      Initialized      : Boolean   := False)
      return W_Prog_Id;
   --  @param Vars a set of variables
   --  @param Params transformation parameters
   --  @param Scope the scope in which these variables are considered. it will
   --     be used to determine whether or not variables are initialized.
   --  @param Exclude_Top_Pred entity of for which we do not want to assume the
   --     top predicate.
   --  @param Initialized True if all variables sould be considered
   --     initialized.
   --  @result Why3 program assuming the dynamic invariant of variables from
   --     Vars. As well as all variables used in their dynamic invariant.

   procedure Assume_Value_Of_Constants
     (Why_Expr : in out W_Prog_Id;
      Scope    :        Entity_Id;
      Params   :        Transformation_Params);
   --  Go through Why_Expr to find all the Ada node referencing constants with
   --  no variable input to assume their definition.
   --  ??? This is especially needed for record aggregates containing floating
   --      point numbers and should not be needed anymore once floating point
   --      numbers are properly handled by solvers.

   function Check_No_Memory_Leaks_At_End_Of_Scope
     (Decls : List_Id)
      return W_Prog_Id;
   --  Go through the list of declarations Decls and generate checks that no
   --  variable leads to a resource leak at the end of its scope. This function
   --  follows the same traversal structure as Check_No_Owning_Decl in
   --  SPARK_Definition.

   function Check_Scalar_Range
     (Params : Transformation_Params;
      N      : Entity_Id;
      Base   : Opt_Type_Kind_Id)
      return W_Prog_Id
   with Pre => (if No (Base) then Is_OK_Static_Range (Get_Range (N)));
   --  Generate checks for the bounds of a range as well as a
   --  range check that the range_constraint is compatible with the subtype.
   --  Returns the empty program if both Base and N have a static
   --  range_constraint.
   --  @param Params transformation parameters
   --  @param N calling Get_Range on N should get the range to check.
   --  @param Base type against which N's bounds should be checked if any.
   --  @return a program that checks that no error can appear while computing
   --  N's bounds and that they are in Base's range.

   function Check_Subtype_Indication
     (Params   : Transformation_Params;
      N        : Node_Id;
      Sub_Type : Type_Kind_Id)
      return W_Prog_Id;
   --  Generate checks for bounds of the range_constraint in Sub_Typ as well as
   --  a range check that the range_constraint in Sub_Typ is compatible with
   --  the subtype. Returns the empty program if N is not a scalar subtype,
   --  or is a scalar subtype with a static range_constraint.

   function Check_Type_With_DIC
     (Params : Transformation_Params;
      Ty     : Type_Kind_Id)
      return W_Prog_Id
   with Pre => May_Need_DIC_Checking (Ty);
   --  Generate checks for absence of runtime errors in the default initial
   --  condition. It also checks that the DIC holds for default values of the
   --  type.
   --  @param Params transformation parameters
   --  @param N a type with a defult initial condition that needs to be checked
   --  @return a program that checks that no error can appear in N's DIC
   --          and it holds for default values of type N.

   procedure Compute_Borrow_At_End_Value
     (Check_Node    : Entity_Id := Empty;
      W_Brower      : W_Term_Id;
      Expr          : N_Subexpr_Id;
      Borrowed_Expr : Opt_N_Subexpr_Id := Empty;
      Reconstructed : out W_Term_Id;
      Checks        : out W_Statement_Sequence_Id);
   --  Expr should be a path. Reconstruct Borrowed_Expr, or the root of Expr
   --  if Borrowed_Expr is not a prefix of Expr, updated so that the path
   --  represented by Expr is set to W_Brower and store it is Reconstructed.
   --  If Check_Node is not Empty, Checks contains a sequence of predicate
   --  checks to ensure that all predicates traversed during the reconstruction
   --  of the expression hold.
   --
   --  For example, if Expr is Func (X.F (I).G, Z).H and Borrowed_Expr is X.F
   --  the following expression is stored in Reconstructed:
   --  { x with f =>
   --      set x.f i { (get x.f i) with g =>
   --          Func.borrowed_at_end (get x.f i).g z
   --               { func (get x.f i).g z with h => w_brower } } }
   --
   --  If the types of F, G, and H have a predicate, Checks contains:
   --    check_predicate_h w_brower;
   --    check_predicate_g
   --     (Func.borrowed_at_end (get x.f i).g z
   --          { func (get x.f i).g z with h => w_brower });
   --    check_predicate_f
   --     (set x.f i { (get x.f i) with g =>
   --          Func.borrowed_at_end (get x.f i).g z
   --               { func (get x.f i).g z with h => w_brower } });

   function Compute_Default_Check
     (Ada_Node         : Node_Id;
      Ty               : Type_Kind_Id;
      Params           : Transformation_Params;
      At_Declaration   : Boolean := False;
      Include_Subtypes : Boolean := False;
      Decl_Node        : Opt_N_Declaration_Id := Empty)
      return W_Prog_Id
   with Pre => (if not Include_Subtypes
                then Can_Be_Default_Initialized (Retysp (Ty)));
   --  @param Ada_Node node to which the checks should be attached
   --  @param Ty The type for which we want to check the default expression
   --  @param Params Transformation parameters
   --  @param At_Declaration If At_Declaration is True, assume all DICs
   --         that apply to ancestors Ty and check the one of Ty if it shall be
   --         checked at declaration. Otherwise, assume all DICs applying to
   --         Ty that should be checked at declaration and check all those
   --         which shall be checked at use.
   --  @param Include_Subtypes True if we also check any subtype of Ty. In
   --         particular, if Ty is a record type with defaulted discriminants,
   --         we only assume the value of its discriminants to be the defaults
   --         if Include_Subtypes is false.
   --  @param Decl_Node If we are checking the declaration of a type whose
   --         default initial value is checked at declaration, Decl_Node is
   --         the node of Ty's declaration.
   --  @result Why3 code to check for absence of runtime errors in default
   --         initialization of Expr of type Ty.

   function Compute_Default_Init
     (Expr             : W_Term_Id;
      Ty               : Type_Kind_Id;
      Params           : Transformation_Params := Body_Params;
      Skip_Last_Cond   : W_Term_Id := False_Term;
      Use_Pred         : Boolean := True;
      Include_Subtypes : Boolean := False)
      return W_Pred_Id
   with Pre => (if not Include_Subtypes
                then Can_Be_Default_Initialized (Retysp (Ty)));
   --  @param Expr Expression for which we want the default initialization
   --  @param Ty The type of the expression Expr
   --  @param Params Transformation parameters
   --  @param Skip_Last_Cond Do not assume the top-level
   --         Default_Initial_Condition of Ty if any.
   --  @param Use_Pred Use the precomputed predicate for Ty's default initial
   --         assumption
   --  @param Include_Subtypes True if Expr can be of any subtype of Ty. In
   --         particular, if Ty is a record type with defaulted discriminants,
   --         we only assume the value of its discriminants to be the defaults
   --         if Include_Subtypes is false.
   --  @result The default initial assumption of type Ty over Expr

   function Compute_Dynamic_Predicate
     (Expr          : W_Term_Id;
      Ty            : Type_Kind_Id;
      Params        : Transformation_Params := Body_Params;
      Top_Predicate : W_Term_Id := True_Term)
      return W_Pred_Id;
   --  @param Expr Why3 term expression on which to express the dynamic
   --     predicate.
   --  @param Ty type with the dynamic invariant
   --  @param Params transformation parameters
   --  @param Top_Predicate True to ignore the top-level predicate of Ty
   --  @result Why3 predicate expressing the dynamic predicate of type [Ty]
   --     over [Expr].

   function Compute_Dynamic_Invariant
     (Expr             : W_Term_Id;
      Ty               : Type_Kind_Id;
      Params           : Transformation_Params;
      Initialized      : W_Term_Id := True_Term;
      Only_Var         : W_Term_Id := True_Term;
      Top_Predicate    : W_Term_Id := True_Term;
      Include_Type_Inv : W_Term_Id := True_Term;
      Use_Pred         : Boolean := True)
      return W_Pred_Id;
   --  @param Expr Why3 expression on which to express the dynamic invariant
   --  @param Ty type of expression [Expr]
   --  @param Initialized true term iff Expr is known to be initialized. If
   --     Expr has an initialization wrapper type, then Initialized is not
   --     used.
   --  @param Only_Var true term iff the dynamic invariant should only consider
   --     the variable parts of [Expr].
   --  @param Top_Predicate true term iff the dynamic invariant should consider
   --     the toplevel type predicate possibly associated with [Ty].
   --  @param Include_Type_Inv true term iff the dynamic invariant should
   --     consider the non-local type invariants possibly associated with [Ty].
   --  @param Params transformation parameters
   --  @param Use_Pred True iff the named predicate should be used
   --  @result Why3 predicate expressing the dynamic invariant of type [Ty]
   --     over [Expr].

   procedure Compute_Dynamic_Invariant
     (Expr             :        W_Term_Id;
      Ty               :        Type_Kind_Id;
      Params           :        Transformation_Params;
      Initialized      :        W_Term_Id;
      Only_Var         :        W_Term_Id;
      Top_Predicate    :        W_Term_Id;
      Include_Type_Inv :        W_Term_Id;
      Use_Pred         :        Boolean;
      New_Preds_Module :        W_Module_Id;
      T                :    out W_Pred_Id;
      Loc_Incompl_Acc  :        Ada_To_Why_Ident.Map;
      New_Incompl_Acc  : in out Ada_To_Why_Ident.Map;
      Expand_Incompl   :        Boolean)
     with Post => (if not Use_Pred and T /= True_Pred then
                   Type_Needs_Dynamic_Invariant (Ty));
   --  Same as above except that the result is stored inside the out parameter
   --  T. Additional parameters are:
   --  @param New_Preds_Module the module that should be used to store new
   --    predicate symbols if there is one.
   --  @param Loc_Incompl_Acc the set of predicate names from the local scope.
   --  @param New_Incompl_Acc new predicate symbols introduced for the type,
   --    they are also in the local scope.
   --  @param Expand_Incompl true if dynamic predicates for values of
   --    incomplete types should be expanded.

   function Compute_Dynamic_Inv_And_Initialization
     (Expr             : W_Term_Id;
      Ty               : Type_Kind_Id;
      Params           : Transformation_Params;
      Initialized      : W_Term_Id := True_Term;
      Only_Var         : W_Term_Id := True_Term;
      Top_Predicate    : Boolean := True;
      Include_Type_Inv : W_Term_Id := True_Term)
      return W_Pred_Id;
   --  Same as Compute_Dynamic_Invariant but also add the initialization if
   --  Expr is an initialization wrapper type and Initialized is true.
   --  @param Initialized true term iff Expr is known to be initialized. If
   --     Expr has an initialization wrapper type, then should only be True if
   --     Expr is at least partially Initialized.

   function Compute_Is_Moved_Property
     (Expr     : W_Term_Id;
      Ty       : Type_Kind_Id;
      Use_Pred : Boolean := True)
      return W_Pred_Id
   with Pre => Contains_Allocated_Parts (Ty);
   --  @param Expr term on which to check all pointers are moved
   --  @param Ty corresponding Ada type
   --  @param Use_Pred True iff the predicate __is_moved should be called
   --  @result predicate expressing that all pointers in [Expr] are moved

   function Compute_Moved_Relation
     (Expr1    : W_Term_Id;
      Expr2    : W_Term_Id;
      Ty       : Type_Kind_Id;
      Use_Pred : Boolean := True)
      return W_Pred_Id
   with Pre => Contains_Allocated_Parts (Ty);
   --  @param Expr1 term corresponding to the new value of an object
   --  @param Expr2 term corresponding to the old value of the same object
   --  @param Ty corresponding Ada type
   --  @param Use_Pred True iff the predicate __moved_relation should
   --         be called
   --  @result predicate expressing that all pointers in [Expr1] are moved,
   --          while all other subcomponents retain their value from [Expr2]

   function Compute_Top_Level_Type_Invariant
     (Expr     : W_Term_Id;
      Ty       : Type_Kind_Id;
      Params   : Transformation_Params := Body_Params;
      Use_Pred : Boolean := True)
      return W_Pred_Id
   with Pre => Eq_Base (Type_Of_Node (Retysp (Ty)), Get_Type (+Expr));
   --  @param Expr Why3 term expression on which to express the type invariant
   --  @param Ty type with the type invariant
   --  @param Params transformation parameters
   --  @param Use_Pred True iff the named predicate should be used
   --  @result Why3 predicate expressing the type invariant of type [Ty] over
   --          [Expr].

   function Compute_Type_Invariant
     (Expr         : W_Term_Id;
      Ty           : Type_Kind_Id;
      Params       : Transformation_Params := Body_Params;
      On_External  : Boolean := False;
      On_Internal  : Boolean := False;
      Include_Comp : Boolean := True;
      Use_Pred     : Boolean := True)
      return W_Pred_Id
   with Pre => (On_Internal or On_External)
     and then (if On_External then not Include_Comp);
   --  @param Expr Why3 term expression on which to express the type invariant
   --  @param Ty type with the type invariant
   --  @param Params transformation parameters
   --  @param On_External True if invariants of types declared outside the
   --         current compilation unit should be considered. In this case,
   --         there might be type invariants inside access-to-incomplete types
   --         that would be ignored in Compute_Type_Invariant, so Include_Comp
   --         should be False (there is no tool restriction for external
   --         types).
   --  @param On_Internal True if invariants of types declared in the current
   --         compilation unit should be considered.
   --  @param Include_Comp False if we do not care about the invariants of
   --         composite types. Invariants of parents of Ty are still included.
   --  @param Use_Pred False if the predicate function introduced for Ty's
   --         top-level invariant should not be used.
   --  @result Why3 predicate expressing the type invariant of type [Ty] and
   --          of all its parts and ancestors over [Expr].

   function Count_Numerical_Variants (E : Callable_Kind_Id) return Natural;
   --  Compute the number of numerical variants of a subprogram or entry if any

   function Get_Pure_Logic_Term_If_Possible
     (Expr          : N_Subexpr_Id;
      Expected_Type : W_Type_Id)
      return W_Term_Id;
   --  If Expr can be translated into a pure logic term (without dereference),
   --  return this term. Otherwise, return Why_Empty.

   function Get_Variants_Exprs
     (E      : Callable_Kind_Id;
      Domain : EW_Domain;
      Params : Transformation_Params)
      return W_Expr_Array
   with Post =>
       Get_Variants_Exprs'Result'Length = Count_Numerical_Variants (E);
   --  Translate the expressions of variants of a subprogram

   function Get_Variants_Ids (E : Callable_Kind_Id) return W_Expr_Array
     with Post =>
       Get_Variants_Ids'Result'Length = Count_Numerical_Variants (E);
   --  Compute the names to be used for initial values of variants of a
   --  subprogram or entry. The returned array only contains identifiers, we
   --  use the type W_Expr_Array to be able to share the handling whether we
   --  use ids or the expressions directly.

   function Havoc_Borrowed_Expression
     (Brower : Constant_Or_Variable_Kind_Id)
      return W_Prog_Id;
   --  Construct a program which havocs a borrowed expression. After the havoc,
   --  we get information about potential updates from the borrower by
   --  assuming that its pledge (relation between the borrower and the borrowed
   --  expression) holds. We also check here that we have not broken any
   --  constraints on the borrowed object during the borrow.

   function Havoc_Borrowed_From_Block
     (N : N_Block_Statement_Id)
      return W_Statement_Sequence_Id;
   --  Havoc all entities borrowed in the block

   function Insert_Predicate_Check
     (Ada_Node      : Node_Id;
      Check_Ty      : Type_Kind_Id;
      W_Expr        : W_Prog_Id;
      Top_Predicate : W_Term_Id := True_Term)
      return W_Prog_Id;
   --  @param Ada_Node node to which the check is attached
   --  @param Check_Ty type whose predicate needs to be checked
   --  @param W_Expr Why3 expression on which to check the predicate
   --  @param Top_Predicate True to ignore the top-level predicate of Check_Ty
   --  @result Why3 program that performs the check and returns [W_Expr]

   function Insert_Invariant_Check
     (Ada_Node : Node_Id;
      Check_Ty : Type_Kind_Id;
      W_Expr   : W_Prog_Id;
      Var_Ent  : Opt_Object_Kind_Id := Empty)
      return W_Prog_Id;
   --  @param Ada_Node node to which the check is attached
   --  @param Check_Ty type whose invariant needs to be checked
   --  @param W_Expr Why3 expression on which to check the invariant
   --  @param Var_Ent entity of the corresponding variable if W_Expr is an
   --         array in split form.
   --  @result Why3 program that performs the check and returns [W_Expr]

   function New_Equality_Of_Preserved_Parts
     (Ty           : Type_Kind_Id;
      Expr1, Expr2 : W_Term_Id)
      return W_Pred_Id;
   --  Return a predicate stating that the (immutable) discriminants,
   --  array bounds, and is_null field of unconstrained types are equal in
   --  Expr1 and Expr2. If Ty is an anonymous access type, also assume the
   --  bounds and discriminants of the designated type.
   --  This is used to assume that these parts are preserved by the borrow
   --  both in the borrower and in the borrowed expression.

   function New_Predicate_Check
     (Ada_Node         : Node_Id;
      Ty               : Type_Kind_Id;
      W_Expr           : W_Expr_Id;
      On_Default_Value : Boolean := False;
      Top_Predicate    : W_Term_Id := True_Term)
      return W_Prog_Id;
   --  @param Ada_Node node to which the check is attached
   --  @param Ty type whose predicate needs to be checked
   --  @param W_Expr Why3 expression on which to check the predicate
   --  @param On_Default_Value True iff this predicate check applies to the
   --    default value for a type
   --  @param Top_Predicate True to ignore the top-level predicate of Ty
   --  @return Why3 program that performs the check

   function Range_Expr
     (N           : Node_Id;
      T           : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params;
      T_Type      : W_Type_OId := Why_Empty)
      return W_Expr_Id;
   --  Given an N_Range node N and a Why expr T, create an expression
   --  low <= T <= high
   --  where "low" and "high" are the lower and higher bounds of N.
   --  T_Type is the base type in which the comparisons take
   --  place (e.g. int, real). If it is not set, it is deduced from
   --  the bounds' type.

   function Transform_Attribute_Old
     (Expr   : N_Subexpr_Id;
      Domain : EW_Domain;
      Params : Transformation_Params)
      return W_Expr_Id;
   --  Translate Expr'Old into Why

   function Transform_Declarations_Block
     (L : List_Id;
      Core : W_Prog_Id)
      return W_Prog_Id;
   --  Translate the Declarations block of Block statement or subprogram to a
   --  sequence of Why expressions; dynamic type declarations are translated
   --  to assert/assume statements, object declarations to assignment
   --  statements
   --  @param L a list of declarations
   --  @param Core an expression to which the statements resulting from L are
   --    prepended

   function Transform_Declarations (L : List_Id) return W_Prog_Id;
   --  Transform the declarations in the list

   function Transform_Discrete_Choices
     (Choices      : List_Id;
      Choice_Type  : Opt_Type_Kind_Id;
      Matched_Expr : W_Expr_Id;
      Cond_Domain  : EW_Domain;
      Params       : Transformation_Params)
      return W_Expr_Id;
   --  Return the guard that corresponds to a branch. In programs, also
   --  generate a check that dynamic choices are in the subtype Choice_Type.

   function Transform_Discrete_Choices
     (Choices      : List_Id;
      Choice_Type  : Opt_Type_Kind_Id;
      Matched_Expr : W_Term_Id;
      Params       : Transformation_Params)
      return W_Pred_Id
   is (+Transform_Discrete_Choices
          (Choices, Choice_Type, +Matched_Expr, EW_Pred, Params));

   function Transform_Expr
     (Expr           : N_Subexpr_Id;
      Expected_Type  : W_Type_Id;
      Domain         : EW_Domain;
      Params         : Transformation_Params;
      No_Pred_Checks : Boolean := False)
      return W_Expr_Id;
   --  Compute an expression in Why having the expected type for the given Ada
   --  expression node. The formal "Domain" decides if we return a predicate,
   --  term or program. If Ref_Allowed is True, then references are allowed,
   --  for example in the context of a program (whether the domain is EW_Prog
   --  for program text or EW_Pred/EW_Term for contract). If Ref_Allowed is
   --  False, then references are not allowed, for example in the context of an
   --  axiom or a logic function definition. If No_Pred_Checks is False,
   --  predicate checks will be emitted on expressions annotated with
   --  Relaxed_Initialization.

   function Transform_Prog
     (Expr           : N_Subexpr_Id;
      Expected_Type  : W_Type_Id;
      Params         : Transformation_Params;
      Checks         : Boolean := True;
      No_Pred_Checks : Boolean := False)
      return W_Prog_Id
   is
     (+Transform_Expr
        (Expr,
         Expected_Type,
         (if Checks then EW_Prog else EW_Pterm),
         Params,
         No_Pred_Checks));

   function Transform_Term
     (Expr          : N_Subexpr_Id;
      Expected_Type : W_Type_Id;
      Params        : Transformation_Params)
      return W_Term_Id
   is
     (+Transform_Expr (Expr, Expected_Type, EW_Term, Params));

   function Transform_Pred
     (Expr          : N_Subexpr_Id;
      Expected_Type : W_Type_Id;
      Params        : Transformation_Params)
      return W_Pred_Id
   is
     (+Transform_Expr (Expr, Expected_Type, EW_Pred, Params));

   function Transform_Expr
     (Expr           : N_Subexpr_Id;
      Domain         : EW_Domain;
      Params         : Transformation_Params;
      No_Pred_Checks : Boolean := False)
      return W_Expr_Id;
   --  Same as above, but derive the Expected_Type from the Ada Expr

   function Transform_Prog
     (Expr           : N_Subexpr_Id;
      Params         : Transformation_Params;
      Checks         : Boolean := True;
      No_Pred_Checks : Boolean := False)
      return W_Prog_Id
   is
     (+Transform_Expr
        (Expr,
         (if Checks then EW_Prog else EW_Pterm),
         Params,
         No_Pred_Checks));

   function Transform_Term
     (Expr   : N_Subexpr_Id;
      Params : Transformation_Params)
      return W_Term_Id
   is
     (+Transform_Expr (Expr, EW_Term, Params));

   function Transform_Pred
     (Expr   : N_Subexpr_Id;
      Params : Transformation_Params)
      return W_Pred_Id
   is
     (+Transform_Expr (Expr, EW_Pred, Params));

   function Transform_Expr_With_Actions
     (Expr          : N_Subexpr_Id;
      Actions       : List_Id;
      Expected_Type : W_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params)
      return W_Expr_Id;
   --  Same as Transform_Expr, but takes into account the declarations of
   --  constants in Actions, to create a suitable variable map for translating
   --  Expr.

   function Transform_Identifier
     (Params   : Transformation_Params;
      Expr     : Node_Id;
      Ent      : Entity_Id;
      Domain   : EW_Domain;
      Selector : Selection_Kind := Why.Inter.Standard)
      return W_Expr_Id;
   --  Transform an Ada identifier to a Why item (take care of enumeration
   --  literals, boolean values etc)
   --
   --  This also deals with volatility, so that an object with a Async_Writers
   --  is suitably havoc'd before being read.

   function Transform_Pragma
     (Prag  : N_Pragma_Id;
      Force : Boolean)
      return W_Prog_Id;
   --  Returns the Why program for pragma.
   --  @param Prag The pragma to translate into Why3.
   --  @param Force True to force the translation of the pragma, for those
   --     pragmas normally translated elsewhere like preconditions and
   --     postconditions.
   --  @return The translated pragma into Why3.

   procedure Transform_Pragma_Check
     (Stmt    :     N_Pragma_Id;
      Force   :     Boolean;
      Expr    : out N_Subexpr_Id;
      Runtime : out W_Prog_Id;
      Pred    : out W_Pred_Id);
   --  Translates a pragma Check into Why3.
   --  @param Stmt The pragma Check to translate.
   --  @param Force True to force the translation of the pragma, even for those
   --     pragmas normally translated elsewhere like preconditions and
   --     postconditions.
   --  @param Expr Expression on which the check is performed, for locating the
   --     VC in Why3.
   --  @param Runtime On exit, Why3 program for checking absence of run-time
   --     errors in the pragma, and possibly getting a program value.
   --  @param Pred On exit, Why3 proposition corresponding to the pragma.

   function Transform_Pragma_Check
     (Prag  : N_Pragma_Id;
      Force : Boolean)
      return W_Prog_Id;
   --  Returns the Why program for pragma Check. As most assertion pragmas
   --  (like Assert or Assume) are internally rewritten by semantic analysis
   --  into pragma Check, this is where these are translated.
   --  @param Prag The pragma Check to translate into Why3.
   --  @param Force True to force the translation of the pragma, even for those
   --     pragmas normally translated elsewhere like preconditions and
   --     postconditions.
   --  @return The translated pragma into Why3.

   function Transform_Simple_Return_Expression
     (Expr        : N_Subexpr_Id;
      Subp        : Entity_Id;
      Return_Type : W_Type_Id)
      return  W_Prog_Id;
   --  Transform a simple return statement returning the expression Expr

   function Transform_Statements_And_Declarations
     (Stmts_And_Decls : List_Id)
      return W_Prog_Id;
   --  Transforms a list of statements and declarations into a Why expression.
   --  An empty list is transformed into the void expression.

   procedure Transform_Statement_Or_Declaration_In_List
     (Stmt_Or_Decl :        Node_Id;
      Seq          : in out W_Statement_Sequence_Id);
   --  Transform the next statement or declaration Stmt_Or_Decl, inside a
   --  list of statements and declarations. Seq is the transformation of the
   --  previous statements and declarations in the list.

   procedure Variables_In_Default_Init
     (Ty        :        Type_Kind_Id;
      Variables : in out Flow_Id_Sets.Set)
   with Post => Variables'Old.Is_Subset (Of_Set => Variables);
   --  @param Ty a type
   --  @param Variables used in the expression for Ty's default initialization

   procedure Variables_In_Dynamic_Predicate
     (Ty        :        Type_Kind_Id;
      Variables : in out Flow_Id_Sets.Set)
   with Pre  => Has_Predicates (Ty),
        Post => Variables'Old.Is_Subset (Of_Set => Variables);
   --  @param Ty a type with a predicate
   --  @param Variables used in the expression for Ty's predicate

   procedure Variables_In_Dynamic_Invariant
     (Ty        :        Type_Kind_Id;
      Variables : in out Flow_Id_Sets.Set)
   with Post => Variables'Old.Is_Subset (Of_Set => Variables);
   --  @param Ty a type
   --  @param Variables used in the expression for Ty's dynamic invariant

   procedure Variables_In_Type_Invariant
     (Ty        :        Type_Kind_Id;
      Variables : in out Flow_Id_Sets.Set)
   with Pre  => Has_Invariants_In_SPARK (Ty),
        Post => Variables'Old.Is_Subset (Of_Set => Variables);
   --  @param Ty a type with a visible type invariant
   --  @param Variables used in the expression for Ty's invariant

   function Void_Sequence return W_Statement_Sequence_Id;
   --  Returns a sequence statement with only one void statement (this avoids
   --  visible calls to New_Statement_Sequence for non sequential statements).

   function Warn_On_Dead_Branch
     (N     : N_Subexpr_Id;
      W     : W_Prog_Id;
      Phase : Transformation_Phase)
      return W_Prog_Id;
   --  In cases where we want to detect unreachable branches, wrap program
   --  expression W with a warning by proof on reachability. Otherwise simply
   --  return W (which may or not be a program in that case).

   function Warn_On_Dead_Code
     (N     : Node_Id;
      W     : W_Prog_Id;
      Phase : Transformation_Phase)
      return W_Prog_Id;
   --  Same as Warn_On_Dead_Branch except for dead code

   function Warn_On_Inconsistent_Assume (N : Node_Id) return W_Prog_Id;
   --  In cases where we want to detect inconsistent pragma Assume, attempt to
   --  issue a warning if the path is dead at this point.

   ----------------------------------------
   -- Attributes Old, Loop_Entry, Result --
   ----------------------------------------

   --  Expressions X'Old and F'Result are normally expanded into references to
   --  saved values of variables by the frontend, but this expansion does not
   --  apply to the original postcondition. It is this postcondition which
   --  is translated by gnat2why into a program to detect possible run-time
   --  errors, therefore a special mechanism is needed to deal with expressions
   --  X'Old and F'Result.

   Result_Name       : W_Identifier_Id := Why_Empty;
   Result_Is_Mutable : Boolean := False;
   --  Name to use for occurrences of F'Result in the postcondition. It should
   --  be equal to Why_Empty when we are not translating a postcondition of a
   --  function.

   Self_Name       : W_Identifier_Id := Why_Empty;
   Self_Is_Mutable : Boolean := False;
   --  Name to use to refer to the state (i.e. fields) of a protected object.
   --  It should be equal to empty when we are not generating code for a
   --  protected subprogram.

   function Bind_From_Mapping_In_Prog
     (Params : Transformation_Params;
      Map    : Ada_To_Why_Ident.Map;
      Expr   : W_Prog_Id)
      return W_Prog_Id;
   --  Bind names from Map to their corresponding values, obtained by
   --  transforming the expression node associated to the name in Map, in Expr.
   --  This is used to bind names for 'Old and 'Loop_Entry attribute reference
   --  to their value.

   function Bind_From_Mapping_In_Expr
     (Params : Transformation_Params;
      Map    : Ada_To_Why_Ident.Map;
      Expr   : W_Expr_Id;
      Domain : EW_Domain;
      Subset : Node_Sets.Set;
      As_Old : Boolean := False)
      return W_Expr_Id;
   --  Same as above but only bind the nodes from Subset. If As_Old is True,
   --  the expressions in Map should be evaluated in the pre state.

private

   Incompl_Access_Dyn_Inv_Map : Ada_To_Why_Ident.Map;
   --  Map storing predicates for invariants of access to incomplete types

end Gnat2Why.Expr;
