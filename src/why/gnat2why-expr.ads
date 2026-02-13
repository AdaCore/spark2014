------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - E X P R                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
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

with Ada.Containers;
with Checked_Types;        use Checked_Types;
with Common_Containers;    use Common_Containers;
with Flow_Types;           use Flow_Types;
with Gnat2Why.Util;        use Gnat2Why.Util;
with Nlists;               use Nlists;
with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Util;           use SPARK_Util;
with SPARK_Util.Types;     use SPARK_Util.Types;
with Types;                use Types;
with Why.Conversions;      use Why.Conversions;
with Why.Gen.Binders;      use Why.Gen.Binders;
with Why.Gen.Expr;         use Why.Gen.Expr;
with Why.Gen.Terms;        use Why.Gen.Terms;
with Why.Ids;              use Why.Ids;
with Why.Inter;            use Why.Inter;
with Why.Sinfo;            use Why.Sinfo;
with Why.Types;            use Why.Types;

package Gnat2Why.Expr is

   procedure Assume_Declaration_Of_Entity
     (E             : Extended_Object_Kind_Id;
      Params        : Transformation_Params;
      Initialized   : Boolean;
      Top_Predicate : Boolean;
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
      Valid         : W_Term_Id := Why_Empty;
      Only_Var      : Boolean := True;
      Top_Predicate : Boolean := True) return W_Prog_Id;
   --  @param Expr Why3 expression on which to assume the dynamic invariant
   --  @param Ty type of expression [Expr]
   --  @param Valid a term encoding the validity tree of Expr if any
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
      Initialized      : Boolean := False) return W_Prog_Id;
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
      Scope    : Entity_Id;
      Params   : Transformation_Params);
   --  Go through Why_Expr to find all the Ada node referencing constants with
   --  no variable input to assume their definition.
   --  ??? This is especially needed for record aggregates containing floating
   --      point numbers and should not be needed anymore once floating point
   --      numbers are properly handled by solvers.

   function Check_Scalar_Range
     (Params : Transformation_Params; N : Node_Id; Base : Type_Kind_Id)
      return W_Prog_Id;
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
     (Params : Transformation_Params; N : Node_Id; Sub_Type : Type_Kind_Id)
      return W_Prog_Id;
   --  Generate checks for bounds of the range_constraint in Sub_Typ as well as
   --  a range check that the range_constraint in Sub_Typ is compatible with
   --  the subtype. Returns the empty program if N is not a scalar subtype,
   --  or is a scalar subtype with a static range_constraint.

   function Check_Type_With_DIC
     (Params : Transformation_Params; Ty : Type_Kind_Id) return W_Prog_Id
   with Pre => May_Need_DIC_Checking (Ty);
   --  Generate checks for absence of runtime errors in the default initial
   --  condition. It also checks that the DIC holds for default values of the
   --  type.
   --  @param Params transformation parameters
   --  @param Ty a type with a default initial condition
   --            that needs to be checked
   --  @return a program that checks that no error can appear in N's DIC
   --          and it holds for default values of type N.

   function Check_Type_With_Iterable
     (Params : Transformation_Params; Ty : Type_Kind_Id) return W_Prog_Id;
   --  Generate checks for absence of runtime errors for
   --  executing a quantified expression over the elements of
   --  a value of (Ty) in any context.
   --  @param Params transformation parameters
   --  @param Ty a type with Iterable aspect
   --  @return a program that checks that no error can occur
   --          when executing a quantified expression in any context.

   generic
      with procedure Process (Ada_Node : Node_Id; Inv : W_Pred_Id);
   procedure Process_Type_Invariants_For_Subprogram
     (E           : Entity_Id;
      Params      : Transformation_Params;
      For_Input   : Boolean;
      Exceptional : Boolean := False;
      Scop        : Entity_Id)
   with
     Pre =>
       (Is_Subprogram_Or_Entry (E) or Ekind (E) = E_Subprogram_Type)
       and then (if Exceptional then not For_Input);
   --  Call Process on all invariant that should be checked for the subprogram
   --  E. Ada_Node is used to localize the check. It can be a formal, a global,
   --  or E itself to model the result of the call.
   --  @param E Entity of a subprogram or entry.
   --  @param Params the transformation parameters
   --  @param For_Input True if we are interested in inputs of E, False if we
   --         are interested in its outputs.
   --  @param Exceptional True if we are interested in outputs of E on
   --         exceptional paths.
   --  @param Scop local scope used to exclude checks on locally assumed
   --         invariants.

   function Check_Type_Invariants_For_Subprogram
     (E           : Entity_Id;
      Ada_Node    : Node_Id;
      Params      : Transformation_Params;
      For_Input   : Boolean;
      Exceptional : Boolean := False) return W_Prog_Id;
   --  Checks all invariants produced by
   --  Process_Type_Invariants_For_Subprogram. Localize the checks on Ada_Node.
   --  Use Current_Subp as a scope.

   procedure Compute_Borrow_At_End_Value
     (Check_Node    : Entity_Id := Empty;
      W_Brower      : W_Term_Id;
      Expr          : N_Subexpr_Id;
      Borrowed_Expr : Opt_N_Subexpr_Id := Empty;
      Params        : Transformation_Params;
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
      Include_Subtypes : Boolean := False) return W_Prog_Id
   with
     Pre =>
       (if not Include_Subtypes then Can_Be_Default_Initialized (Retysp (Ty)));
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
   --  @result Why3 code to check for absence of runtime errors in default
   --         initialization of Expr of type Ty.

   function Compute_Default_Init
     (Expr             : W_Term_Id;
      Ty               : Type_Kind_Id;
      Params           : Transformation_Params := Body_Params;
      Skip_Last_Cond   : W_Term_Id := False_Term;
      Use_Pred         : Boolean := True;
      Include_Subtypes : Boolean := False) return W_Pred_Id
   with
     Pre =>
       (if not Include_Subtypes then Can_Be_Default_Initialized (Retysp (Ty)));
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
      Top_Predicate : W_Term_Id := True_Term) return W_Pred_Id;
   --  @param Expr Why3 term expression on which to express the dynamic
   --     predicate.
   --  @param Ty type with the dynamic invariant
   --  @param Params transformation parameters
   --  @param Top_Predicate True to ignore the top-level predicate of Ty
   --  @result Why3 predicate expressing the dynamic predicate of type [Ty]
   --     over [Expr].

   function Compute_Dynamic_Invariant
     (Expr           : W_Term_Id;
      Ty             : Type_Kind_Id;
      Params         : Transformation_Params;
      Initialized    : W_Term_Id := True_Term;
      Valid          : W_Term_Id := Why_Empty;
      Only_Var       : W_Term_Id := True_Term;
      Top_Predicate  : W_Term_Id := True_Term;
      All_Global_Inv : Boolean := True;
      Use_Pred       : Boolean := True) return W_Pred_Id;
   --  @param Expr Why3 expression on which to express the dynamic invariant
   --  @param Ty type of expression [Expr]
   --  @param Initialized true term iff Expr is known to be initialized. If
   --     Expr has an initialization wrapper type, then Initialized is not
   --     used.
   --  @param Valid validity flag of Expr if it is potentially invalid,
   --     Why_Empty otherwise.
   --  @param Only_Var true term iff the dynamic invariant should only consider
   --     the variable parts of [Expr].
   --  @param Top_Predicate true term iff the dynamic invariant should consider
   --     the toplevel type predicate possibly associated with [Ty].
   --  @param All_Global_Inv true if the dynamic invariant should consider all
   --     the non-local type invariants possibly associated with [Ty]. If it is
   --     False, non-local invariants relaxed for parameters of Current_Subp
   --     are excluded.
   --  @param Use_Pred True iff the named predicate should be used
   --  @result Why3 predicate expressing the dynamic invariant of type [Ty]
   --     over [Expr]. Current_Subp is used as a scope for the type invariants.
   --     It is used to assume local type invariants which are always True in a
   --     given scope.

   procedure Compute_Dynamic_Invariant
     (Expr              : W_Term_Id;
      Ty                : Type_Kind_Id;
      Params            : Transformation_Params;
      Initialized       : W_Term_Id;
      Valid             : W_Term_Id;
      Only_Var          : W_Term_Id;
      Top_Predicate     : W_Term_Id;
      All_Global_Inv    : W_Term_Id;
      Inv_Scop          : Node_Id;
      Inv_Subp          : Node_Id;
      Use_Pred          : Boolean;
      New_Preds_Module  : W_Module_Id;
      T                 : out W_Pred_Id;
      Loc_Incompl_Acc   : Ada_To_Why_Ident.Map;
      New_Incompl_Acc   : in out Ada_To_Why_Ident.Map;
      Loc_Incompl_Acc_R : Ada_To_Why_Ident.Map;
      New_Incompl_Acc_R : in out Ada_To_Why_Ident.Map;
      Expand_Incompl    : Boolean)
   with
     Pre  =>
       (if Present (Inv_Subp)
        then Inv_Scop = Inv_Subp and then Is_False_Boolean (+All_Global_Inv)),
     Post =>
       (if not Use_Pred and T /= True_Pred
        then Type_Needs_Dynamic_Invariant (Ty));
   --  Same as above except that the result is stored inside the out parameter
   --  T. The boolean flag All_Global_Inv is replaced by a boolean term so
   --  the function can be used to generate the dynamic invariant predicate.
   --  Additional parameters are:
   --  @param Inv_Scop scope for the type invariants. It is used to assume
   --    local type invariants which are always True in a given scope. It
   --    might be empty when generating the dynamic invariant predicate for
   --    Ty. In this case, no local invariant is assumed.
   --  @param Inv_Subp optional subprogram parameter. It is set to Inv_Scop
   --    when non local type invariants should be assumed on a case-by-case
   --    basis depending on whether or not they are relaxed for parameters in
   --    the current scope. When it is set, non-local invariants should not be
   --    assumed globally (All_Global_Inv should be False).
   --  @param New_Preds_Module the module that should be used to store new
   --    predicate symbols if there is one.
   --  @param Loc_Incompl_Acc the set of predicate names from the local scope.
   --  @param New_Incompl_Acc new predicate symbols introduced for the type,
   --    they are also in the local scope.
   --  @param Loc_Incompl_Acc_R same as Loc_Incompl_Acc but for init wrappers
   --  @param New_Incompl_Acc_R same as New_Incompl_Acc but for init wrappers
   --  @param Expand_Incompl true if dynamic predicates for values of
   --    incomplete types should be expanded.

   function Compute_Dynamic_Inv_And_Initialization
     (Expr           : W_Term_Id;
      Ty             : Type_Kind_Id;
      Params         : Transformation_Params;
      Initialized    : W_Term_Id := True_Term;
      Valid          : W_Term_Id := Why_Empty;
      Only_Var       : W_Term_Id := True_Term;
      Top_Predicate  : Boolean := True;
      All_Global_Inv : Boolean := True) return W_Pred_Id;
   --  Same as Compute_Dynamic_Invariant but also add the initialization if
   --  Expr is an initialization wrapper type and Initialized is true.
   --  @param Initialized true term iff Expr is known to be initialized. If
   --     Expr has an initialization wrapper type, then should only be True if
   --     Expr is at least partially Initialized.

   function Compute_Guard_For_Exceptions
     (Choices : List_Id; Exc_Id : W_Identifier_Id; Domain : EW_Domain)
      return W_Expr_Id
   with Pre => Nkind (First (Choices)) /= N_Others_Choice;
   --  Compute the guard corresponding to an exceptional case

   function Compute_Is_Moved_Or_Reclaimed
     (Expr : W_Term_Id; Tree : W_Term_Id; Ty : Type_Kind_Id) return W_Pred_Id;
   --  Predicate expressing that Expr is entirely reclaimed or moved as per the
   --  move tree Tree. Tree is a move tree for type Ty.

   function Compute_Is_Reclaimed_For_Ownership
     (Expr : W_Term_Id; Ty : Type_Kind_Id; For_Check : Boolean)
      return W_Pred_Id;
   --  Check reclamation on a type annotated with ownership. If For_Check is
   --  True, consider the confirming annotation. Otherwise confirming
   --  annotations are ignored.

   function Compute_Top_Level_Type_Invariant
     (Expr     : W_Term_Id;
      Ty       : Type_Kind_Id;
      Params   : Transformation_Params := Body_Params;
      Use_Pred : Boolean := True) return W_Pred_Id
   with Pre => Eq_Base (Type_Of_Node (Retysp (Ty)), Get_Type (+Expr));
   --  @param Expr Why3 term expression on which to express the type invariant
   --  @param Ty type with the type invariant
   --  @param Params transformation parameters
   --  @param Use_Pred True iff the named predicate should be used
   --  @result Why3 predicate expressing the type invariant of type [Ty] over
   --          [Expr].

   type Invariant_Kind is (Globally_Assumed, Locally_Assumed, For_Check);

   function Compute_Type_Invariant
     (Expr         : W_Term_Id;
      Ty           : Type_Kind_Id;
      Kind         : Invariant_Kind;
      Params       : Transformation_Params := Body_Params;
      Scop         : Entity_Id := Empty;
      Subp         : Entity_Id := Empty;
      Include_Comp : Boolean := True;
      Use_Pred     : Boolean := True) return W_Pred_Id
   with
     Pre  =>
       (case Kind is
          when Globally_Assumed =>
            No (Scop) and then No (Subp) and then not Include_Comp,
          when Locally_Assumed  => Present (Scop),
          when For_Check        => Present (Scop) and then Include_Comp),
     Post =>
       (if Kind = For_Check
        then
          Is_True_Boolean (+Compute_Type_Invariant'Result)
          /= Invariant_Check_Needed (Ty, Subp, Scop));
   --  @param Expr Why3 term expression on which to express the type invariant
   --  @param Ty type with the type invariant
   --  @param Kind can be Globally_Assumed for invariants assumed globally in
   --         the main unit, Locally_Assumed for invariants assumed in Scop
   --         and For_Check for invariants that need to be checked in Scop or
   --         globally in the unit if Scop is Empty.
   --  @param Params transformation parameters
   --  @param Scop scope of the invariant. Shall be set for Locally_Assumed and
   --         For_Check.
   --  @param Subp optional subprogram. If supplied, it is used to exclude
   --         invariants that are relaxed for For_Checks and to include
   --         globally assumed invariants that are not relaxed for
   --         Locally_Assumed.
   --  @param Include_Comp False if we do not care about the invariants of
   --         components of composite types. Invariants of parents of Ty are
   --         still included.
   --  @param Use_Pred False if the predicate function introduced for Ty's
   --         top-level invariant should not be used.
   --  @result Why3 predicate expressing the type invariant of type [Ty] and
   --          of all its parts and ancestors over [Expr].

   function Count_Numerical_Variants (E : Callable_Kind_Id) return Natural;
   --  Compute the number of numerical variants of a subprogram or entry if any

   function Expected_Type_For_Move_Tree
     (N : Node_Or_Entity_Id) return Type_Kind_Id;
   --  N is an expression or object which can be moved. Return the type that
   --  should be used to querry its move tree. It might not be the type of N
   --  on case of view conversions or unconstrained formal parameters.

   function Finalization_Actions
     (Scope   : Node_Id;
      Exiting : Local_CFG.Vertex;
      Params  : Transformation_Params) return W_Statement_Sequence_Id;
   --  From a scope a <<scope>> with attached finalization actions,
   --  translate the individual finalization actions to perform at exit. That
   --  is,
   --  * For Handled sequence of statements with a finally section, the
   --    translation of the code within the section.
   --  * For block statements or entity with bodies, havocs all borrowed
   --    expressions. After each individual havoc, we get information about
   --    potential updates from the borrower by assuming that its pledge
   --    (relation between the borrower and the borrowed expression) holds. We
   --    also check here that we have not broken any constraints on the
   --    borrowed object during the borrow.
   --  * For block statements or entities with bodies, checks that no variable
   --    leads to a resource leak.
   --
   --  Scope is considered to be exited from Exiting, to filter out borrowers
   --  not updated on any local control path to Exiting from the havoced
   --  borrows.

   function Finalization_Actions_On_Jump
     (Jump : Node_Id; Params : Transformation_Params) return W_Prog_Id;
   --  Translate the finalization actions for a static jump (goto/exit/return).
   --  This is equivalent to the sequence of programs resulting from
   --  Finalization_Actions for all exited scopes, in order.

   function Get_Variants_Exprs
     (E : Callable_Kind_Id; Domain : EW_Domain; Params : Transformation_Params)
      return W_Expr_Array
   with
     Post => Get_Variants_Exprs'Result'Length = Count_Numerical_Variants (E);
   --  Translate the expressions of variants of a subprogram

   function Get_Variants_Ids (E : Callable_Kind_Id) return W_Expr_Array
   with Post => Get_Variants_Ids'Result'Length = Count_Numerical_Variants (E);
   --  Compute the names to be used for initial values of variants of a
   --  subprogram or entry. The returned array only contains identifiers, we
   --  use the type W_Expr_Array to be able to share the handling whether we
   --  use ids or the expressions directly.

   function Insert_Predicate_Check
     (Ada_Node      : Node_Id;
      Check_Ty      : Type_Kind_Id;
      W_Expr        : W_Prog_Id;
      Top_Predicate : Boolean := True) return W_Prog_Id;
   --  @param Ada_Node node to which the check is attached
   --  @param Check_Ty type whose predicate needs to be checked
   --  @param W_Expr Why3 expression on which to check the predicate
   --  @param Top_Predicate True to ignore the top-level predicate of Check_Ty
   --  @result Why3 program that performs the check and returns [W_Expr]

   function Insert_Invariant_Check
     (Ada_Node   : Node_Id;
      Check_Ty   : Type_Kind_Id;
      W_Expr     : W_Prog_Id;
      Var_Ent    : Opt_Object_Kind_Id := Empty;
      Check_Info : Check_Info_Type := New_Check_Info) return W_Prog_Id;
   --  @param Ada_Node node to which the check is attached
   --  @param Check_Ty type whose invariant needs to be checked
   --  @param W_Expr Why3 expression on which to check the invariant
   --  @param Var_Ent entity of the corresponding variable if W_Expr is an
   --         array in split form.
   --  @param Check_Info information for the check
   --  @result Why3 program that performs the check and returns [W_Expr]

   function New_Move_Tree_Access_For_Identitier
     (Ent : Entity_Id) return W_Expr_Id;
   --  Create an access to the move tree for Ent

   function New_Equality_Of_Preserved_Parts
     (Ty : Type_Kind_Id; Expr1, Expr2 : W_Term_Id) return W_Pred_Id;
   --  Return a predicate stating that the (immutable) discriminants,
   --  array bounds, and is_null and is_moved fields of unconstrained types are
   --  equal in Expr1 and Expr2. If Ty is an anonymous access type, also assume
   --  the bounds and discriminants of the designated type.
   --  This is used to assume that these parts are preserved by the borrow
   --  both in the borrower and in the borrowed expression.

   function New_Predicate_Check
     (Ada_Node         : Node_Id;
      Ty               : Type_Kind_Id;
      W_Expr           : W_Expr_Id;
      On_Default_Value : Boolean := False;
      Top_Predicate    : Boolean := True) return W_Prog_Id;
   --  @param Ada_Node node to which the check is attached
   --  @param Ty type whose predicate needs to be checked
   --  @param W_Expr Why3 expression on which to check the predicate
   --  @param On_Default_Value True iff this predicate check applies to the
   --    default value for a type
   --  @param Top_Predicate True to ignore the top-level predicate of Ty
   --  @return Why3 program that performs the check

   function Range_Expr
     (N      : Node_Id;
      T      : W_Expr_Id;
      Domain : EW_Domain;
      Params : Transformation_Params;
      T_Type : W_Type_OId := Why_Empty) return W_Expr_Id;
   --  Given an N_Range node N and a Why expr T, create an expression
   --  low <= T <= high
   --  where "low" and "high" are the lower and higher bounds of N.
   --  T_Type is the base type of T (e.g. int, real). The comparison will be
   --  done in a range accomodating both T_Type (if set) and the bounds' type.

   function Transform_Attribute_Old
     (Expr              : N_Subexpr_Id;
      Domain            : EW_Domain;
      Params            : Transformation_Params;
      No_Validity_Check : Boolean := False) return W_Expr_Id;
   --  Translate Expr'Old into Why

   function Transform_Declarations_Block
     (L : List_Id; Core : W_Prog_Id; Params : Transformation_Params)
      return W_Prog_Id;
   --  Translate the Declarations block of Block statement or subprogram to a
   --  sequence of Why expressions; dynamic type declarations are translated
   --  to assert/assume statements, object declarations to assignment
   --  statements
   --  @param L a list of declarations
   --  @param Core an expression to which the statements resulting from L are
   --    prepended
   --  @param Params transformation parameters

   function Transform_Declarations
     (L : List_Id; Params : Transformation_Params) return W_Prog_Id;
   --  Transform the declarations in the list

   function Transform_Discrete_Choices
     (Choices      : List_Id;
      Choice_Type  : Opt_Type_Kind_Id;
      Matched_Expr : W_Expr_Id;
      Cond_Domain  : EW_Domain;
      Params       : Transformation_Params) return W_Expr_Id;
   --  Return the guard that corresponds to a branch. In programs, also
   --  generate a check that dynamic choices are in the subtype Choice_Type.

   function Transform_Discrete_Choices
     (Choices      : List_Id;
      Choice_Type  : Opt_Type_Kind_Id;
      Matched_Expr : W_Term_Id;
      Params       : Transformation_Params) return W_Pred_Id
   is (+Transform_Discrete_Choices
          (Choices, Choice_Type, +Matched_Expr, EW_Pred, Params));

   function Transform_Expr
     (Expr              : N_Subexpr_Id;
      Expected_Type     : W_Type_Id;
      Domain            : EW_Domain;
      Params            : Transformation_Params;
      No_Init_Check     : Boolean := False;
      No_Validity_Check : Boolean := False) return W_Expr_Id;
   --  Compute an expression in Why having the expected type for the given Ada
   --  expression node. The formal "Domain" decides if we return a predicate,
   --  term or program. If Ref_Allowed is True, then references are allowed,
   --  for example in the context of a program (whether the domain is EW_Prog
   --  for program text or EW_Pred/EW_Term for contract). If Ref_Allowed is
   --  False, then references are not allowed, for example in the context of an
   --  axiom or a logic function definition. If No_Init_Check is True, the
   --  expression does not need to be initialized and predicate checks and
   --  initialization checks for discriminants will not be emitted on
   --  expressions annotated with Relaxed_Initialization. If No_Validity_Check
   --  is True, do not emit validity check if expr is potentially invalid.

   function Transform_Prog
     (Expr              : N_Subexpr_Id;
      Expected_Type     : W_Type_Id;
      Params            : Transformation_Params;
      Checks            : Boolean := True;
      No_Init_Check     : Boolean := False;
      No_Validity_Check : Boolean := False) return W_Prog_Id
   is (+Transform_Expr
          (Expr,
           Expected_Type,
           (if Checks then EW_Prog else EW_Pterm),
           Params,
           No_Init_Check,
           No_Validity_Check));

   function Transform_Term
     (Expr          : N_Subexpr_Id;
      Expected_Type : W_Type_Id;
      Params        : Transformation_Params) return W_Term_Id
   is (+Transform_Expr (Expr, Expected_Type, EW_Term, Params));

   function Transform_Pred
     (Expr          : N_Subexpr_Id;
      Expected_Type : W_Type_Id;
      Params        : Transformation_Params) return W_Pred_Id
   is (+Transform_Expr (Expr, Expected_Type, EW_Pred, Params));

   function Transform_Expr
     (Expr              : N_Subexpr_Id;
      Domain            : EW_Domain;
      Params            : Transformation_Params;
      No_Init_Check     : Boolean := False;
      No_Validity_Check : Boolean := False) return W_Expr_Id;
   --  Same as above, but derive the Expected_Type from the Ada Expr

   function Transform_Prog
     (Expr              : N_Subexpr_Id;
      Params            : Transformation_Params;
      Checks            : Boolean := True;
      No_Init_Check     : Boolean := False;
      No_Validity_Check : Boolean := False) return W_Prog_Id
   is (+Transform_Expr
          (Expr,
           (if Checks then EW_Prog else EW_Pterm),
           Params,
           No_Init_Check,
           No_Validity_Check));

   function Transform_Term
     (Expr : N_Subexpr_Id; Params : Transformation_Params) return W_Term_Id
   is (+Transform_Expr (Expr, EW_Term, Params));

   function Transform_Pred
     (Expr : N_Subexpr_Id; Params : Transformation_Params) return W_Pred_Id
   is (+Transform_Expr (Expr, EW_Pred, Params));

   function Transform_Expr_With_Actions
     (Expr          : N_Subexpr_Id;
      Actions       : List_Id;
      Expected_Type : W_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id;
   --  Same as Transform_Expr, but takes into account the declarations of
   --  constants in Actions, to create a suitable variable map for translating
   --  Expr.

   function Transform_Identifier
     (Params            : Transformation_Params;
      Expr              : Node_Id;
      Ent               : Entity_Id;
      Domain            : EW_Domain;
      Selector          : Selection_Kind := Why.Inter.Standard;
      No_Init_Check     : Boolean := False;
      No_Validity_Check : Boolean := False) return W_Expr_Id;
   --  Transform an Ada identifier to a Why item.
   --
   --  This also deals with volatility, so that an object with a Async_Writers
   --  is suitably havoc'd before being read.

   procedure Transform_Potentially_Invalid_Expr
     (Expr       : N_Subexpr_Id;
      Domain     : EW_Domain;
      Params     : Transformation_Params;
      Context    : in out Ref_Context;
      W_Expr     : out W_Expr_Id;
      Valid_Flag : out W_Expr_Id;
      As_Old     : Boolean := False)
   with Pre => Is_Potentially_Invalid_Expr (Expr);
   --  Transform a potentially invalid expression. Store the transformed
   --  expression into W_Expr and its valid flag into Valid_Flag.
   --  Constant bindings might be introduced in Context as necessary.

   function Transform_Potentially_Invalid_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params;
      Context       : in out Ref_Context;
      Valid_Flag    : out W_Expr_Id;
      No_Checks     : Boolean := False) return W_Expr_Id
   with Pre => (if No_Checks then Is_Potentially_Invalid_Expr (Expr));
   --  Transform an expression that might be potentially invalid. Return the
   --  transformed expression and set Valid_Flag to the valid flag that should
   --  be used for it.
   --  Constant bindings might be introduced in Context as necessary.
   --  If No_Checks is True, do not emit checks on conversion to Expected_Type.

   function Transform_Pragma
     (Prag : N_Pragma_Id; Params : Transformation_Params; Force : Boolean)
      return W_Prog_Id
   with Pre => not Is_Pragma_Assert_And_Cut (Prag);
   --  Returns the Why program for pragma.
   --  @param Prag The pragma to translate into Why3.
   --  @param Params transformation parameters
   --  @param Force True to force the translation of the pragma, for those
   --     pragmas normally translated elsewhere like preconditions and
   --     postconditions.
   --  @return The translated pragma into Why3.

   procedure Transform_Pragma_Check
     (Stmt    : N_Pragma_Id;
      Params  : Transformation_Params;
      Expr    : out N_Subexpr_Id;
      Runtime : out W_Prog_Id;
      Pred    : out W_Pred_Id;
      Msg     : out String_Id);
   --  For a pragma Check, produces the components of its translation into Why3
   --  @param Stmt The pragma Check to translate.
   --  @param Params transformation parameters
   --  @param Expr Expression on which the check is performed, for locating the
   --     VC in Why3.
   --  @param Runtime On exit, Why3 program for checking absence of run-time
   --     errors in the pragma, and possibly getting a program value.
   --  @param Pred On exit, Why3 proposition corresponding to the pragma.
   --  @param Msg On exit, user message associated to the pragma, or No_String.

   function Transform_Pragma_Check
     (Prag : N_Pragma_Id; Params : Transformation_Params; Force : Boolean)
      return W_Prog_Id
   with Pre => not Is_Pragma_Assert_And_Cut (Prag);
   --  Returns the Why program for pragma Check. As most assertion pragmas
   --  (like Assert or Assume) are internally rewritten by semantic analysis
   --  into pragma Check, this is where these are translated.
   --  @param Prag The pragma Check to translate into Why3.
   --  @param Params transformation parameters
   --  @param Force True to force the translation of the pragma, even for those
   --     pragmas normally translated elsewhere like preconditions and
   --     postconditions.
   --  @return The translated pragma into Why3.

   function Transform_Simple_Return_Expression
     (Expr        : N_Subexpr_Id;
      Subp        : Entity_Id;
      Return_Type : W_Type_Id;
      Params      : Transformation_Params) return W_Prog_Id;
   --  Transform a simple return statement returning the expression Expr

   function Transform_Handled_Statements
     (N : Node_Id; Params : Transformation_Params) return W_Prog_Id;
   --  Transforms an handled list of statements into a Why expression

   procedure Transform_Statement_Or_Declaration_In_List
     (Stmt_Or_Decl : Node_Id;
      Params       : Transformation_Params;
      Seq          : in out W_Statement_Sequence_Id);
   --  Transform the next statement or declaration Stmt_Or_Decl, inside a
   --  list of statements and declarations. Seq is the transformation of the
   --  previous statements and declarations in the list.

   procedure Variables_In_Default_Init
     (Ty : Type_Kind_Id; Variables : in out Flow_Id_Sets.Set)
   with Post => Variables'Old.Is_Subset (Of_Set => Variables);
   --  @param Ty a type
   --  @param Variables used in the expression for Ty's default initialization

   procedure Variables_In_Dynamic_Predicate
     (Ty : Type_Kind_Id; Variables : in out Flow_Id_Sets.Set)
   with
     Pre  => Has_Predicates (Ty),
     Post => Variables'Old.Is_Subset (Of_Set => Variables);
   --  @param Ty a type with a predicate
   --  @param Variables used in the expression for Ty's predicate

   procedure Variables_In_Dynamic_Invariant
     (Ty : Type_Kind_Id; Variables : in out Flow_Id_Sets.Set; Scop : Entity_Id)
   with Post => Variables'Old.Is_Subset (Of_Set => Variables);
   --  @param Ty a type
   --  @param Scop scope in which the dynamic invariant is computed.
   --  @param Variables used in the expression for Ty's dynamic invariant

   procedure Variables_In_Type_Invariant
     (Ty : Type_Kind_Id; Variables : in out Flow_Id_Sets.Set)
   with
     Pre  => Has_Invariants_In_SPARK (Ty),
     Post => Variables'Old.Is_Subset (Of_Set => Variables);
   --  @param Ty a type with a visible type invariant
   --  @param Variables used in the expression for Ty's invariant

   function Warn_On_Dead_Branch
     (N       : N_Subexpr_Id;
      W       : W_Prog_Id;
      Phase   : Transformation_Phase;
      Do_Warn : Boolean) return W_Prog_Id;
   --  In cases where we want to detect unreachable branches, wrap program
   --  expression W with a warning by proof on reachability. Otherwise simply
   --  return W (which may or not be a program in that case).

   function Warn_On_Dead_Code
     (N       : Node_Id;
      W       : W_Prog_Id;
      Phase   : Transformation_Phase;
      Do_Warn : Boolean) return W_Prog_Id;
   --  Same as Warn_On_Dead_Branch except for dead code

   function Warn_On_Inconsistent_Assume
     (N : Node_Id; Do_Warn : Boolean) return W_Prog_Id;
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

   function Get_Valid_Id_For_Result (Fun : Entity_Id) return W_Term_Id;
   --  Return the valid flag used for Result_Name if Fun has a potentially
   --  invalid result. Otherwise, return Why_Empty.

   Self_Name       : W_Identifier_Id := Why_Empty;
   Self_Is_Mutable : Boolean := False;
   --  Name to use to refer to the state (i.e. fields) of a protected object.
   --  It should be equal to empty when we are not generating code for a
   --  protected subprogram.

   function Bind_From_Mapping_In_Prog
     (Params       : Transformation_Params;
      Map          : Ada_To_Why_Ident.Map;
      Expr         : W_Prog_Id;
      Old_Prefixes : Boolean := False) return W_Prog_Id;
   --  Bind names from Map to their corresponding values, obtained by
   --  transforming the expression node associated to the name in Map, in Expr.
   --  This is used to bind names for 'Old and 'Loop_Entry attribute reference
   --  to their value.
   --  If Old_Prefix is set to True, the expression nodes are assumed to be
   --  prefix of 'Old attributes. The definition of the bindings are guarded
   --  by the evaluation condition for conditionally evaluated 'Old attributes.

   function Bind_From_Mapping_In_Prog
     (Params : Transformation_Params;
      Map    : Loop_Entry_Values;
      Expr   : W_Prog_Id) return W_Prog_Id;
   --  Same as above but takes a pair of maps as provided for the 'Loop_Entry
   --  attribute reference.

   function Bind_From_Mapping_In_Expr
     (Params       : Transformation_Params;
      Map          : Ada_To_Why_Ident.Map;
      Expr         : W_Expr_Id;
      Domain       : EW_Domain;
      Subset       : Node_Sets.Set;
      Old_Prefixes : Boolean := False) return W_Expr_Id
   with Pre => Domain = EW_Prog or else not Old_Prefixes;
   --  Same as above but only bind the nodes from Subset.

   function Bind_From_Mapping_In_Expr
     (Params    : Transformation_Params;
      Expr      : W_Expr_Id;
      N         : Node_Id;
      Name      : W_Identifier_Id;
      Domain    : EW_Domain;
      Condition : W_Prog_Id := Why_Empty) return W_Expr_Id
   with Pre => Domain = EW_Prog or else No (Condition);
   --  Introduce a mapping from the name Name to the Ada expression or entity N
   --  in Expr. If Condition is provided, the name is defined only under the
   --  condition being true. This is only pertinent in program domain, to guard
   --  RTE checks.

private
   use type Ada.Containers.Count_Type;

   Incompl_Access_Dyn_Inv_Map : Ada_To_Why_Ident.Map;
   --  Map storing predicates for invariants of access to incomplete types

   Incompl_Access_Dyn_Inv_Map_R : Ada_To_Why_Ident.Map;
   --  Same but for predicates of init wrappers

   procedure Get_Item_From_Expr
     (Pattern     : Item_Type;
      Expr        : W_Expr_Id;
      Constr_Expr : W_Expr_Id := Why_Empty;
      Context     : in out Ref_Context;
      Args        : out W_Expr_Array;
      Need_Store  : out Boolean;
      Reuse_Discr : Boolean := False)
   with
     Pre  =>
       (if Pattern.Kind = DRecord and then Pattern.Constr.Present
        then Constr_Expr /= Why_Empty)
       and
         Args'Length
         >= Item_Array_Length ((1 => Pattern), Ignore_Init_And_Valid => True),
     Post => Need_Store or Context.Length = Context.Length'Old;
   --  Split a Why expression into parts that will be used to call a
   --  subprogram. The parts are stored in Args. Pattern is an item
   --  representing the expected form of the formal parameter. Its variable
   --  parts are used for the names of the new references introduced for the
   --  variable parts. Mappings for these variables are stored in Context.
   --  Need_Store is set to True if at least one new reference is introduced.
   --  If Reuse_Discr is True, the identifier for the discriminant in Pattern
   --  is the one from the actual, no need to introduce a mapping for it.
   --  This procedure does not handle the Init flag.

   function Reconstruct_Formal_From_Item
     (Pattern : Item_Type; Pre_Expr : W_Expr_Id) return W_Prog_Id;
   --  From an item Pattern holding the identifiers for the mutable parts of
   --  a formal parameter and its previous value Pre_Expr, reconstruct an
   --  expression for the new version of the formal.

end Gnat2Why.Expr;
