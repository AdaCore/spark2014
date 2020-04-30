------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - E X P R                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Ada.Characters.Handling;        use Ada.Characters.Handling;
with Ada.Containers;                 use Ada.Containers;
with Ada.Containers.Vectors;
with Ada.Strings;
with Ada.Strings.Equal_Case_Insensitive;
with Ada.Strings.Fixed;              use Ada.Strings.Fixed;
with Ada.Text_IO;  --  For debugging, to print info before raising an exception
with Checks;                         use Checks;
with Debug;
with Elists;                         use Elists;
with Errout;                         use Errout;
with Flow.Analysis.Antialiasing;     use Flow.Analysis.Antialiasing;
with Flow_Dependency_Maps;           use Flow_Dependency_Maps;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Refinement;                use Flow_Refinement;
with Flow_Utility;                   use Flow_Utility;
with Flow_Utility.Initialization;    use Flow_Utility.Initialization;
with GNAT.Source_Info;
with GNATCOLL.Symbols;               use GNATCOLL.Symbols;
with Gnat2Why_Args;
with Gnat2Why.Error_Messages;        use Gnat2Why.Error_Messages;
with Gnat2Why.Expr.Loops;            use Gnat2Why.Expr.Loops;
with Gnat2Why.Expr.Loops.Exits;
with Gnat2Why.Subprograms;           use Gnat2Why.Subprograms;
with Gnat2Why.Tables;                use Gnat2Why.Tables;
with Namet;                          use Namet;
with Nlists;                         use Nlists;
with Opt;                            use type Opt.Warning_Mode_Type;
with Rtsfind;                        use Rtsfind;
with Sem;
with Sinput;                         use Sinput;
with Snames;                         use Snames;
with SPARK_Definition;               use SPARK_Definition;
with SPARK_Definition.Annotate;      use SPARK_Definition.Annotate;
with SPARK_Util.External_Axioms;     use SPARK_Util.External_Axioms;
with SPARK_Util.Hardcoded;           use SPARK_Util.Hardcoded;
with SPARK_Util.Subprograms;         use SPARK_Util.Subprograms;
with Stand;                          use Stand;
with Stringt;                        use Stringt;
with String_Utils;                   use String_Utils;
with Uintp;                          use Uintp;
with Urealp;                         use Urealp;
with VC_Kinds;                       use VC_Kinds;
with Why;                            use Why;
with Why.Atree.Builders;             use Why.Atree.Builders;
with Why.Atree.Accessors;            use Why.Atree.Accessors;
with Why.Atree.Mutators;             use Why.Atree.Mutators;
with Why.Atree.Modules;              use Why.Atree.Modules;
with Why.Atree.Tables;               use Why.Atree.Tables;
with Why.Conversions;                use Why.Conversions;
with Why.Gen.Arrays;                 use Why.Gen.Arrays;
with Why.Gen.Binders;                use Why.Gen.Binders;
with Why.Gen.Decl;                   use Why.Gen.Decl;
with Why.Gen.Expr;                   use Why.Gen.Expr;
with Why.Gen.Hardcoded;              use Why.Gen.Hardcoded;
with Why.Gen.Init;                   use Why.Gen.Init;
with Why.Gen.Names;                  use Why.Gen.Names;
with Why.Gen.Progs;                  use Why.Gen.Progs;
with Why.Gen.Pointers;               use Why.Gen.Pointers;
with Why.Gen.Records;                use Why.Gen.Records;
with Why.Gen.Scalars;                use Why.Gen.Scalars;
with Why.Images;                     use Why.Images;
with Why.Unchecked_Ids;              use Why.Unchecked_Ids;

package body Gnat2Why.Expr is

   --  This package handles the translation of expressions and statements to
   --  Why.

   --  -----------------------------
   --  Handling of 'Image and 'Value
   --  -----------------------------
   --
   --  For each scalar type, we introduce functions corresponding to 'Image and
   --  'Value. Logically, the return type of 'Image and the argument type of
   --  'Value should be Standard__String, but this would be circular, as String
   --  depends on a scalar type itself. Therefore, we introduce an abstract
   --  type __image, which is used as return type/argument type of the Why3
   --  functions for 'Image and 'Value. In addition, in the Why3 module for
   --  Standard__String, we generate two conversion functions between __image
   --  and String. The actual translation of the attributes now needs to use
   --  these conversion functions to get an actual String from a scalar, or
   --  to be able to convert a string to a scalar. So X'Image gets converted to
   --
   --  Standard__String.to_string (attr__ATTRIBUTE_IMAGE (to_int (x)))
   --
   --  Finally, to express that 'Value may fail, there is also a program
   --  function that corresponds to 'Value, that has an unprovable
   --  precondition, and "true" as postcondition.

   --  Code pointers:
   --    * Why3 declarations for type __image and the attributes Image
   --      and Value: see file ada__model.mlw.
   --    * Special case for the Standard__String module: see
   --      why-gen-arrays.adb:Declare_Unconstrained_Array
   --    * handling of the attributes: Transform_Attr in this file.

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Apply_Modulus
     (Op     : N_Op;
      E      : Entity_Id;
      T      : W_Expr_Id;
      Domain : EW_Domain) return W_Expr_Id;
   --  If E is a modular type, apply a modulus on T, else return T unchanged.
   --  Beware that for additions, substractions and multiplications on a
   --  modular type with a modulus that is not a power of two, it is not
   --  correct to use this function. Instead, one should directly use
   --  "Transform_Non_Binary_Modular_Operation" to deal with the whole
   --  transformation.
   --  Optimization: if E is a modular type, and Op is a division, do not add
   --  the modulus operation.

   function Assignment_Of_Obj_Decl (N : Node_Id) return W_Prog_Id
   with Pre => Nkind (N) = N_Object_Declaration;
   --  @param N the object declaration
   --  @return an assignment of the declared variable to its initial value

   function Case_Expr_Of_Ada_Node
     (N             : Node_Id;
      Expected_Type : W_Type_OId := Why_Empty;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id;
   --  Build Case expression of Ada Node

   function Check_No_Memory_Leaks
     (Ada_Node           : Node_Id;
      N                  : Node_Or_Entity_Id;
      Is_Uncheck_Dealloc : Boolean := False;
      At_End_Of_Scope    : Boolean := False)
      return W_Prog_Id
   with Pre => (if Nkind (N) = N_Defining_Identifier then Is_Object (N));
   --  @param Ada_Node location for the generated check
   --  @param N either entity for a local object on which to check absence of
   --    memory leak at the end of scope, or lvalue of an assignment (which
   --    includes OUT parameters and actuals of calls to instances of
   --    Ada.Unchecked_Deallocation)
   --  @param Is_Uncheck_Dealloc whether this is a call to an instance of
   --    Ada.Unchecked_Deallocation
   --  @return program checking the absence of memory leak

   function Check_No_Wrap_Around_Modular_Operation
     (Ada_Node   : Node_Id;
      Ada_Type   : Entity_Id;
      Op         : N_Op;
      Left_Opnd  : W_Expr_Id := Why_Empty;
      Right_Opnd : W_Expr_Id;
      Rep_Type   : W_Type_Id;
      Modulus    : Uint) return W_Prog_Id
   with Pre => Present (Ada_Node);
   --  For modular type Ada_Type with annotation No_Wrap_Around, a check must
   --  be emitted on unary operation - and binary operations - + *
   --
   --  @param Ada_Node the node to which the check should be attached
   --  @param Ada_Type type of the Ada node, used to retrieve type Size in bits
   --  @param Op the operation, should be either Minus, Add, Sub or Mul
   --  @param Left_Opnd the left operand of type [Rep_Type], should be empty if
   --     Op is N_Op_Minus.
   --  @param Right_Opnd the right operand of type [Rep_Type]
   --  @param Rep_Type the representation type in which the operation is done.
   --     Both operand should already be converted to this type.
   --  @param Modulus the modulus of the type in which the operation is done
   --  @return the Why3 check expression

   function Check_Type_With_Invariants
     (Params : Transformation_Params;
      N      : Entity_Id) return W_Prog_Id;
   --  Generate checks for absence of runtime errors in the type invariant
   --  expression. It also checks that the invariant holds for default values
   --  of the type.
   --  @param Params transformation parameters
   --  @param N a type with a type invariant visible in SPARK
   --  @return a program that checks that no error can appear in N's type
   --          invariant and that the invariant holds for default values
   --          of type N.

   type Ref_Type is record
      Mutable : Boolean;
      Name    : W_Identifier_Id;
      Value   : W_Expr_Id;
   end record;
   --  Represent a mapping from an identifier Name to an expression Value.
   --  If Mutable is True, the mapping should be a reference.

   package Ref_Type_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Ref_Type);
   subtype Ref_Context is Ref_Type_Vectors.Vector;

   function Compute_Call_Args
     (Call    : Node_Id;
      Domain  : EW_Domain;
      Context : in out Ref_Context;
      Store   : W_Statement_Sequence_Unchecked_Id;
      Params  : Transformation_Params) return W_Expr_Array;
   --  Compute arguments for a function call or procedure call. The node in
   --  argument must have a "Name" field and a "Parameter_Associations" field.
   --  Sometimes, because of type mismatch, or because the actual is a
   --  subcomponent of an object, (mutable) actual parameters of the
   --  call cannot be used directly as parameters of the Why call. In this
   --  case, Compute_Call_Args will also compute mappings for new parameters
   --  as well as some post processing to store them back into the actual
   --  parameters. The mappings are then stored in Context, and the post
   --  processing is stored in Store.

   procedure Compute_Store
     (Pattern        : Item_Type;
      Actual         : Node_Id;
      Need_Store     : Boolean;
      No_Pred_Checks : Boolean;
      Pre_Expr       : W_Expr_Id;
      Store          : W_Statement_Sequence_Unchecked_Id;
      Params         : Transformation_Params);
   --  Compute in Store the sequence of statements necessary to store back
   --  local identifiers of Pattern inside Actual. If Need_Store is True, at
   --  least one new identifier was used for the call. Note that
   --  postprocessing may be needed even if Need_Store is False, to set the
   --  init wrapper flag if any, or to perform predicate checks.
   --  If No_Pred_Checks is True, do not check the predicate of the actual
   --  after the call.

   function Compute_Tag_Check
     (Call   : Node_Id;
      Params : Transformation_Params) return W_Prog_Id;
   --  ???

   function Dynamic_Predicate_Expression
     (Expr      : W_Expr_Id;
      Pred_Subp : Entity_Id;
      Domain    : EW_Domain;
      Params    : Transformation_Params) return W_Expr_Id;
   --  Transform the expression of a dynamic_predicate
   --  @param Expr expression on which the predicate is called
   --  @param Pred_Subp entity of the predicate function
   --  @param Domain Domain where we want to do the transformation
   --  @param Params transformation parameters
   --  @return the translation of the expression contained in the predicate
   --  applied on Expr.

   function Discrete_Choice_Is_Range (Choice : Node_Id) return Boolean;
   --  Return whether Choice is a range ("others" counts as a range)

   function Expected_Type_Of_Prefix (N : Node_Id) return Entity_Id;
   --  The node in argument is the target of an assignment. This function
   --  computes the type of the entity that corresponds to the access.
   --  This may be different from the Etype of the node in case of
   --  unconstrained array types, or discriminant records.

   function Expected_Type_Of_Prefix (N : Node_Id) return W_Type_Id;
   --  Same as above but returns a Why type Id. Note that this may not be
   --  the same as EW_Abstract (Expected_Type_Of_Prefix (N)) on identifiers
   --  which are not in abstract form.

   procedure Get_Item_From_Expr
     (Pattern     : Item_Type;
      Expr        : W_Expr_Id;
      Constr_Expr : W_Expr_Id := Why_Empty;
      Context     : in out Ref_Context;
      Args        : out W_Expr_Array;
      Need_Store  : out Boolean;
      Reuse_Discr : Boolean := False)
   with Pre => (if Pattern.Kind = DRecord and then Pattern.Constr.Present
                then Constr_Expr /= Why_Empty)
     and Args'Length >= To_Binder_Array ((1 => Pattern))'Length
     and Pattern.Init.Present = False,
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

   procedure Get_Item_From_Var
     (Pattern     : in out Item_Type;
      Var         : Item_Type;
      Expr        : W_Expr_Id;
      Constr_Expr : W_Expr_Id := Why_Empty;
      Context     : in out Ref_Context;
      Args        : out W_Expr_Array;
      Need_Store  : out Boolean)
   with Pre => Item_Is_Mutable (Pattern)
     and (if Pattern.Kind = DRecord and then Pattern.Constr.Present
            then Constr_Expr /= Why_Empty)
     and Args'Length >= To_Binder_Array ((1 => Pattern))'Length
     and Pattern.Init.Present = False,
     Post => Need_Store or Context.Length = Context.Length'Old;
   --  Try to reuse parts of the references of the actual Var for the
   --  formal. If the types do not match, fall back to Get_Item_From_Expr. If
   --  Need_Store is True, the Pattern is updated to reference the parts reused
   --  from Var if any.

   procedure Insert_Move_Of_Deep_Parts
     (Stmt    : Node_Id;
      Lhs_Typ : Entity_Id;
      Expr    : in out W_Prog_Id)
   with Pre => Nkind (Stmt) in N_Assignment_Statement
                             | N_Object_Declaration
                             | N_Simple_Return_Statement;
   --  @param Stmt assignment or object declaration or return statement
   --  @param Lhs_Typ expected type for the lhs of the assignment
   --  @param Expr program that contains the translation of the rhs on input,
   --         and inserts moves on output.

   function Insert_Overflow_Check
     (Ada_Node : Node_Id;
      T        : W_Expr_Id;
      In_Type  : Entity_Id;
      Is_Float : Boolean) return W_Expr_Id
     with Pre => Is_Scalar_Type (In_Type);
   --  Inserts an overflow check on top of the Why expression T, using the
   --  bounds of the base type of In_Type. Use Ada_Node for the VC location.

   function Insert_Ref_Context
     (Ada_Call : Node_Id;
      Why_Call : W_Prog_Id;
      Context  : Ref_Context;
      Store    : W_Statement_Sequence_Unchecked_Id) return W_Prog_Id;
   --  Reconstruct the complete sequence needed to model the Ada call Ada_Call.
   --  Why_Call is the actual call in Why3, Context holds the mappings for
   --  the new identifiers used in the call (when actual parameters are
   --  complex), and Store contains the postprocessing steps necessary to store
   --  back the actuals after the call.

   function Is_Simple_Actual (Actual : Node_Id) return Boolean
     with Pre => Nkind (Actual) in N_Subexpr;
   --  Return True if N is a simple enough object so that its binder can
   --  be reused for parameter passing. Basically this is true for simple
   --  identifiers that are not too complex (e.g. not Part_Of or other
   --  complications).

   function Is_Terminal_Node (N : Node_Id) return Boolean;
   --  Decide whether this is a node where we should put a pretty printing
   --  label, or if we should descend further. Basically, everything that's
   --  not a quantifier or conjunction is a terminal node.

   function Move_Expression
     (Expr : Node_Id;
      Tmp  : W_Identifier_Id) return W_Prog_Id;
   --  @param Expr expression with pointers that is moved
   --  @param Tmp identifier storing the value of the expression to move
   --  @return program performing the move, moving all pointers in Expr and
   --          preserving the value of other components

   function New_Assignment
     (Ada_Node : Node_Id := Empty;
      Lvalue   : Node_Id;
      Expr     : W_Prog_Id;
      No_Check : Boolean := False) return W_Prog_Id;
   --  Translate an assignment of the form "Lvalue := Expr" (using Ada_Node
   --  for its source location). If No_Check is True, then no check should be
   --  introduced. This is used for generating code moving an owning object,
   --  that does not correspond to a source code assignment and only updates
   --  the internal is_moved fields, and as such should not lead to the
   --  generation of checks.

   function New_Binary_Op_Expr
     (Op          : N_Binary_Op;
      Left        : W_Expr_Id;
      Right       : W_Expr_Id;
      Left_Type   : Entity_Id;
      Right_Type  : Entity_Id;
      Return_Type : Entity_Id;
      Domain      : EW_Domain;
      Ada_Node    : Node_Id := Empty) return W_Expr_Id
   with Pre => Op in N_Op_Add .. N_Op_Rem;
   --  @param Op arithmetic binary operator
   --  @param Left why expression for the left hand side
   --  @param Right why expression for the right hand side
   --  @param Left_Type Ada Type of the left hand side
   --  @param Right_Type Ada Type of the right hand side
   --  @param Return_Type Ada Type of the result of the operation
   --  @param Domain domain of the operation
   --  @param Ada_Node node associated to the operation
   --  @return a Why3 expression for Left Op Right

   function New_Constrained_Attribute_Expr
     (Prefix : Node_Id;
      Domain : EW_Domain) return W_Expr_Id;
   --  @param Prefix prefix of the 'constrained attribute
   --  @param Domain domain of the expression
   --  @return a Why3 expression Prefix'Constrained

   function New_Predicate_Call
     (Ty     : Entity_Id;
      W_Expr : W_Term_Id;
      Params : Transformation_Params) return W_Pred_Id;
   --  @param Ty type whose predicate needs to be checked
   --  @param W_Expr Why3 expression on which to check the predicate
   --  @param Params transformation parameters
   --  @return Why3 predicate that expressed the check

   function New_Type_Invariant_Call
     (Ty     : Entity_Id;
      W_Expr : W_Term_Id;
      Params : Transformation_Params) return W_Pred_Id;
   --  @param Ty type whose type invariant needs to be checked
   --  @param W_Expr Why3 expression on which to check the invariant
   --  @param Params transformation parameters
   --  @return Why3 predicate that expresses the check

   function New_Invariant_Check
     (Ada_Node         : Node_Id;
      Ty               : Entity_Id;
      W_Expr           : W_Expr_Id;
      On_Default_Value : Boolean := False) return W_Prog_Id;
   --  @param Ada_Node node to which the check is attached
   --  @param Ty type whose invariant needs to be checked
   --  @param W_Expr Why3 expression on which to check the invariant
   --  @param On_Default_Value True iff this invariant check applies to the
   --    default value for a type
   --  @return Why3 program that performs the check

   function One_Level_Access
     (N      : Node_Id;
      Expr   : W_Expr_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;
   --  Compute an access expression for record and array accesses without
   --  considering subexpressions. [N] represents the Ada node of the access,
   --  and [Expr] the Why expression of the prefix.

   function One_Level_Update
     (N       : Node_Id;
      Pref    : W_Expr_Id;
      Value   : W_Expr_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id;
   --  @param N       the Ada node which defines the component to be updated
   --                  (e.g. a record access)
   --  @param Pref    the currently computed prefix, (e.g. the record value
   --                  before the update)
   --  @param Value   the new value of the updated component
   --  @param Domain  the domain
   --  @param Params  the translation params
   --  @return the Why expression which corresponds to the Pref object, but
   --            updated at the point specified by N, with value Value

   function Reconstruct_Expr_From_Item
     (Pattern   : Item_Type;
      Actual    : Node_Id;
      No_Checks : Boolean;
      Pre_Expr  : W_Expr_Id) return W_Prog_Id;
   --  From an item Pattern holding the identifiers for the mutable parts of
   --  an Ada name Actual and the previous value Pre_Expr of Actual, we
   --  reconstruct an expression for the new version of the actual, suitable
   --  for being used in New_Assignment.

   procedure Shift_Rvalue
     (N           : in out Node_Id;
      Expr        : in out W_Expr_Id;
      Last_Access : in out Node_Id;
      Domain      : EW_Domain := EW_Prog);
   --  the input pair (N, Expr) describes an assignment
   --      N := Expr
   --  where N is the Ada node for some Lvalue of the form
   --    Prefix.Acc1.(...).Acc[n-1].Accn := Expr;
   --  The *output* pair (N, Expr) corresponds to the same
   --  assignment, but shifting the Accn to the right side and transforming
   --  it into an update. We obtain
   --    Prefix.Acc1.(...).Acc[n-1] :=
   --         Upd (Prefix.Acc1.(...).Acc[n-1], Accn, Expr)
   --  Last_Access is used as an accumulator to store the last subexpression
   --  which is not a conversion in the parents of N.

   function Transform_Aggregate
     (Params        : Transformation_Params;
      Domain        : EW_Domain;
      Expr          : Node_Id;
      Update_Prefix : Node_Id := Empty) return W_Expr_Id;
   --  Transform an aggregate Expr. It may be called multiple times on the
   --  same Ada node, corresponding to different phases of the translation. The
   --  first time it is called on an Ada node, a logic function is generated
   --  and stored in Ada_To_Why_Func, so that the function and axiom are
   --  generated only once per source aggregate. This function F is used
   --  for generating each translation of this node. The general signature for
   --  F  is:
   --
   --     function F (<params>) : <type of aggregate>
   --
   --     axiom A:
   --        forall R:<type of aggregate>. forall <params>.
   --           R = F(<params>) -> <proposition for the aggregate R>
   --
   --  F takes as in parameters all components passed to the aggregate.
   --  This is simply the list of components for a one-dimensional aggregate,
   --  and it takes into account sub-components for multi-dimensional
   --  aggregates.
   --
   --  ( On the aggregate (1 => X, others => Y), components are {X, Y}.
   --  On the aggregate (1 => (1 => X, others => Y), 2 => Z), components are
   --  {X, Y, Z}.)
   --
   --  In_Delta_Aggregate is True for an aggregate used as argument of a
   --  'Update attribute_reference, and False for a regular aggregate.
   --
   --  If In_Delta_Aggregate is True, there are some additional properties for
   --  the logic function created (F):
   --
   --    a) the prefix array is sent as an extra parameter. "Others" is not
   --       allowed so no parameter for that, instead the values from the
   --       prefix array are used.
   --
   --    b) an extra parameter for every choice, since they can be dynamic,
   --       and an extra pair of parameters for each choice range (high and
   --       low range bounds).
   --
   --    c) the order of the cases in the generated why if statement in the
   --       axiom for the logic function needs to be the _reverse_ of that
   --       given in the aggregate, because associations can duplicate indices,
   --       and the prefix should be updated in the order the associations and
   --       choices are given.
   --
   --  As an example:
   --  Arr'Update(1 .. 3 => 10, 2 => 20, 2 .. 4 => 30, 3 => 40));
   --  is allowed for an array and should mean
   --  Arr(1) = 10 and Arr(2) = 30 and Arr(3) = 40 and Arr(4) = 30

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id;
   --  Translate a single Ada statement into a Why expression

   function Transform_Block_Statement (N : Node_Id) return W_Prog_Id;
   --  ???

   function Transform_Comparison
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;
   --  Transform comparison operations

   function Transform_Concatenation
     (Left               : W_Expr_Id;
      Right              : W_Expr_Id;
      Left_Type          : Entity_Id;
      Right_Type         : Entity_Id;
      Return_Type        : Entity_Id;
      Is_Component_Left  : Boolean;
      Is_Component_Right : Boolean;
      Domain             : EW_Domain;
      Ada_Node           : Node_Id) return W_Expr_Id;
   --  Handle concatenation nodes

   function Transform_Discrete_Choice
     (Choice      : Node_Id;
      Choice_Type : Entity_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id;
   --  For an expression Expr of a discrete type and a discrete Choice, build
   --  the expression that Expr belongs to the range expressed by Choice. In
   --  programs, also generate a check that dynamic choices are in the subtype
   --  Choice_Type.

   function Transform_Delta_Aggregate
     (Ada_Node : Node_Id;
      Pref     : Node_Id;
      Aggr     : Node_Id;
      Domain   : EW_Domain;
      Params   : Transformation_Params) return W_Expr_Id;
   --  Transform either a delta aggregate or an Update attribute

   function Transform_Declaration (Decl : Node_Id) return W_Prog_Id;
   --  Transform a declaration. Return a program that takes into account the
   --  dynamic semantics of the declaration (checks and assumptions).

   function Transform_Expr_Or_Identifier
     (N      : Node_Or_Entity_Id;
      Domain : EW_Domain;
      Params : Transformation_Params)
      return W_Expr_Id
   is (if Nkind (N) = N_Defining_Identifier
       then Transform_Identifier (Params, N, N, Domain)
       else Transform_Expr (N, Domain, Params));
   --  N may be an expression or an identifier. Call the appropriate
   --  translation function.

   function Transform_Quantified_Expression
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;
   --  @return the Why3 expression for SPARK quantified expression [Expr]

   function Transform_Priority_Pragmas (Prag : Node_Id) return W_Prog_Id with
     Pre => Get_Pragma_Id (Prag) in Pragma_Interrupt_Priority |
                                    Pragma_Priority;
   --  @param Prag either a pragma Priority or a pragma Interrupt_priority
   --  @return an expression that checks that the argument of the pragma is in
   --          the required range for this object type and pragma type

   function Transform_Slice
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id) return W_Expr_Id;
   --  Transform a slice Expr

   function Transform_Statement_Or_Declaration
     (Stmt_Or_Decl        : Node_Id;
      Assert_And_Cut_Expr : out Node_Id;
      Assert_And_Cut      : out W_Pred_Id)
      return W_Prog_Id;
   --  Transform the Ada statement into a Why program expression.
   --  @param Assert_And_Cut_Expr Expression in the pragma Assert_And_Cut, if
   --     Stmt_Or_Decl was such a pragma, Empty otherwise.
   --  @param Assert_And_Cut Why3 predicate equivalent of the assertion
   --     expression, if Stmt_Or_Decl was such a pragma, Why_Empty otherwise.
   --  @return the check program expression that corresponds to the assertion
   --     expression.

   function Type_Invariant_Expression
     (Expr     : W_Expr_Id;
      Inv_Subp : Entity_Id;
      Domain   : EW_Domain;
      Params   : Transformation_Params) return W_Expr_Id;
   --  Transform the expression of a type_invariant
   --  @param Expr expression on which the invariant is called
   --  @param Inv_Subp entity of the invariant procedure
   --  @param Domain domain where we want to do the transformation
   --  @param Params transformation parameters
   --  @return the translation of the expression contained in the invariant
   --          applied on Expr.

   procedure Warn_On_Dead_Branch_Condition_Update
     (Cond    : Node_Id;
      Do_Warn : in out Boolean);
   --  Set the condition Do_Warn to False if the Boolean expression Cond is
   --  statically True or False, or it contains a sub-expression X'Valid. As
   --  validity is assumed to be always True in GNATprove, we don't want to
   --  report a spurious warning in that case.

   function Warn_On_Dead_Branch_Or_Code
     (N      : Node_Id;
      W      : W_Expr_Id;
      Branch : Boolean;
      Phase  : Transformation_Phase) return W_Expr_Id;
   --  Shared functionality for warning on dead branch or dead code.

   function Why_Subp_Has_Precondition
     (E        : Entity_Id;
      Selector : Selection_Kind := Why.Inter.Standard) return Boolean
   with Pre => (if Selector = No_Return then Is_Error_Signaling_Procedure (E));
   --  Return true whenever the Why declaration that corresponds to the given
   --  subprogram has a precondition.

   ------------------------------------------
   -- Handling of Expressions with Actions --
   ------------------------------------------

   --  The detection phase currently allows 3 kinds of nodes in actions:
   --    N_Object_Declaration for constants
   --    N_Subtype_Declaration
   --    N_Full_Type_Declaration

   --  Declarations of constant objects are transformed into let-binding in
   --  Why, which is possible in any context (program, term, proposition).

   --  Declarations of types are simply ignored. Indeed, we don't know how to
   --  translate the assignment to type bounds like done in
   --  Transform_Declaration in a proposition context. Note that this choice
   --  can possibly lead to dynamic bounds not known at VC level, if such types
   --  are introduced in actions.

   function Transform_Actions
     (Actions : List_Id;
      Expr    : W_Expr_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id;
   --  Translate a list of Actions, that should consist only in declarations of
   --  constants used in Expr.

   procedure Transform_Actions_Preparation (Actions : List_Id);
   --  Update the symbol table for taking into account the names for
   --  declarations of constants in Actions.

   function Transform_Attr
     (Expr         : Node_Id;
      Domain       : EW_Domain;
      Params       : Transformation_Params;
      Expected_Typ : W_Type_Id) return W_Expr_Id;
   --  Range_Check_Needed is set to True for some attributes (like 'Pos,
   --  'Length, 'Modulus) which return a universal integer, so that we check
   --  the result fits in the actual type used for the node.
   --  @param Expr attribute reference
   --  @param Domain domain where we want to do the transformation
   --  @param Params transformation parameters
   --  @param Expected_Typ expected why3 type of the expression. It only
   --         matters when computing the length attribute of an array type
   --         which has a modular index.
   --  @return the translation of the expression contained in the invariant
   --          applied on Expr.

   procedure Transform_String_Literal
     (Params : Transformation_Params;
      N      : Node_Id);
   --  Create an uninterpreted logic function with no parameters that returns a
   --  string value corresponding to the string literal.

   function Transform_Record_Component_Associations
     (Domain             : EW_Domain;
      Typ                : Entity_Id;
      Assocs             : List_Id;
      Params             : Transformation_Params;
      In_Delta_Aggregate : Boolean := False;
      Init_Wrapper       : Boolean) return W_Field_Association_Array;
   --  Returns a list of updates to be applied to a record value, to
   --  translate either an aggregate or a delta aggregate.
   --  In_Delta_Aggregate is True when translating a delta aggregate.
   --  Associations for discriminants are stored before associations for
   --  normal fields.

   function Transform_Function_Call
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   with Pre => Nkind (Expr) in N_Function_Call | N_Op;
   --  Transform a function call

   function Transform_Enum_Literal
     (Expr   : Node_Id;
      Enum   : Entity_Id;
      Domain : EW_Domain)
      return W_Expr_Id;
   --  Translate an Ada enumeration literal to Why

   function Transform_Compare_Op
     (Op     : N_Op_Compare;
      Ty     : W_Type_Id;
      Domain : EW_Domain) return W_Identifier_Id;
   --  Convert an Ada comparison operator to a Why relation symbol

   function Transform_Membership_Expression
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id) return W_Expr_Id;
   --  Convert a membership expression (N_In or N_Not_In) into a boolean Why
   --  expression.

   function Transform_Array_Equality
     (Op        : N_Op_Compare;
      Left      : W_Expr_Id;
      Right     : W_Expr_Id;
      Left_Type : Entity_Id;
      Domain    : EW_Domain;
      Ada_Node  : Node_Id) return W_Expr_Id;
   --  Translate an equality on arrays into a Why expression, take care of the
   --  different cases (constrained / unconstrained) for each argument.

   function Transform_Array_Comparison
     (Op       : N_Op_Compare;
      Left     : W_Expr_Id;
      Right    : W_Expr_Id;
      Domain   : EW_Domain;
      Ada_Node : Node_Id) return W_Expr_Id;
   --  Translate a comparison on arrays into a Why expression

   function Transform_Array_Logical_Op
     (Op        : N_Binary_Op;
      Left      : W_Expr_Id;
      Right     : W_Expr_Id;
      Left_Type : Entity_Id;
      Domain    : EW_Domain;
      Ada_Node  : Node_Id;
      Do_Check  : Boolean) return W_Expr_Id;
   --  Translate a binary operation on boolean arrays into a Why expression

   function Transform_Array_Negation
     (Right      : W_Expr_Id;
      Right_Type : Entity_Id;
      Domain     : EW_Domain;
      Ada_Node   : Node_Id;
      Do_Check   : Boolean) return W_Expr_Id;
   --  Translate negation on boolean arrays into a Why expression

   --  Returns the Why program for raise statement Stat
   function Transform_Raise (Stat : Node_Id) return W_Prog_Id is
     (+New_VC_Expr (Domain   => EW_Prog,
                    Ada_Node => Stat,
                    Expr     => +New_Identifier (Name => "absurd"),
                    Reason   => VC_Raise))
   with Pre => Nkind (Stat) in
     N_Raise_xxx_Error | N_Raise_Statement | N_Raise_Expression;

   function Transform_Shift_Or_Rotate_Call
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;
   --  @param Expr a call where the callee is a shift or rotate subprogram
   --  @param Domain the domain in which the translation happens
   --  @param Params the translation parameters
   --  @return the Why expression corresponding to the shift or rotate

   function Transform_Non_Binary_Modular_Operation
     (Ada_Node   : Node_Id;
      Ada_Type   : Entity_Id;
      Domain     : EW_Domain;
      Op         : N_Op;
      Left_Opnd  : W_Expr_Id := Why_Empty;
      Right_Opnd : W_Expr_Id;
      Rep_Type   : W_Type_Id;
      Modulus    : Uint) return W_Expr_Id
     with Pre => Modulus < UI_Expon (2, 32);
   --  For non binary modular types, it is incorrect to apply the arithmetic
   --  operations - + * on the base type and then apply the modulus on the
   --  result. The special treatment needed in this case is implemented here.
   --
   --  @param Ada_Type type of the Ada node, used to retrieve type Size in bits
   --  @param Op the operation, should be either Minus, Add, Sub or Mul
   --  @param Left_Opnd the left operand of type [Rep_Type], should be empty if
   --     Op is N_Op_Minus.
   --  @param Right_Opnd the right operand of type [Rep_Type]
   --  @param Rep_Type the representation type in which the operation is done.
   --     Both operand should already be converted to this type.
   --  @param Modulus the modulus of the type in which the operation is done.
   --     It should be a non power of two smaller than 2 ** 32.
   --  @return the Why3 expression corresponding to the operation with
   --     modulus applied. One should not call Apply_Modulus after
   --     calling this function.

   function Has_Visibility_On_Refined
     (Expr : Node_Id;
      E    : Entity_Id)
      return Boolean
   with Pre => Ekind (E) in E_Function | E_Procedure | E_Entry
               and then Entity_Body_In_SPARK (E);
   --  Return True if node Expr can "see" the Refined_Post of entity E

   ---------------------------------
   -- Handling of Local Borrowers --
   ---------------------------------

   function Compute_Assumption_For_Borrow
     (Brower      : Entity_Id;
      Borrowed_Id : W_Identifier_Id;
      Params      : Transformation_Params) return W_Pred_Id;
   --  Compute constraints preserved throughout the life of a borrower

   function New_Pledge_Update_From_Assignment
     (Brower : Entity_Id;
      Path   : Node_Id) return W_Prog_Id;
   --  Create an assignment updating the pledge of a borrower from an update
   --  Path. Brower is either the local borrower in the case of a borrow or
   --  a reborrow, or the subprogram entity when returning from a traversal
   --  function.

   function Transform_Pledge_Call
     (Brower : Entity_Id;
      Def    : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;
   --  Transform a call to a function annotated with a pragma Annotate
   --  (GNATprove, Pledge, ...).
   --  ??? The translation is stronger than the actual function body, so we
   --  may have a proved check failing at runtime if such a call is used in
   --  a negative way.

   -------------------
   -- Apply_Modulus --
   -------------------

   function Apply_Modulus
     (Op     : N_Op;
      E      : Entity_Id;
      T      : W_Expr_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Ty          : constant Entity_Id := Retysp (E);
      Modulus_Val : Uint;
      BV_Type     : W_Type_Id;
   begin
      if Is_Modular_Integer_Type (Ty) and then Op /= N_Op_Divide then
         Modulus_Val := Modulus (Ty);
         BV_Type := Base_Why_Type (Ty);

         --  If the modulus matches the size of the machine integer (for
         --  example a modulus of 2 ** 32 for a 32-bits machine integer),
         --  no modulo operation is needed.

         if Modulus_Val = UI_Expon (2, Modular_Size (Ty)) then
            return T;

         --  Otherwise we perform the modulo on bitvectors

         else
            return New_Call (Name   => MF_BVs (BV_Type).Urem,
                             Domain => Domain,
                             Args   => (1 => T,
                                        2 => New_Modular_Constant
                                               (Value => Modulus_Val,
                                                Typ   => BV_Type)),
                             Typ    => BV_Type);
         end if;

      else
         return T;
      end if;
   end Apply_Modulus;

   ----------------------------
   -- Assignment_Of_Obj_Decl --
   ----------------------------

   function Assignment_Of_Obj_Decl (N : Node_Id) return W_Prog_Id
   is
      Lvalue : Entity_Id := Defining_Identifier (N);
      Rexpr  : constant Node_Id := Expression (N);
   begin

      --  We ignore part_of objects as a first approximation

      if Is_Part_Of_Protected_Object (Lvalue) then
         return +Void;
      end if;

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

      --  Some objects have two declarations, i.e. the partial and full view of
      --  a package level object. In this case, we always use the type of the
      --  partial view.

      if Is_Full_View (Lvalue) then
         Lvalue := Partial_View (Lvalue);
      end if;

      if Present (Rexpr) then
         declare
            Binder   : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, Lvalue);
            Why_Ty   : constant W_Type_Id := Type_Of_Node (Lvalue);
            Why_Expr : W_Prog_Id :=
              +Transform_Expr (Rexpr,
                               Why_Ty,
                               EW_Prog,
                               Params => Body_Params);
            L_Name   : constant String := Full_Name (Lvalue);
            Res      : W_Prog_Id := +Void;

         begin
            pragma Assert (not Binder.Init.Present);

            Insert_Move_Of_Deep_Parts (Stmt    => N,
                                       Lhs_Typ => Etype (Lvalue),
                                       Expr    => Why_Expr);

            --  Init pledge of local borrowers

            if Is_Local_Borrower (Lvalue) then
               Res := New_Pledge_Update_From_Assignment
                 (Brower  => Lvalue,
                  Path    => Rexpr);
            end if;

            case Binder.Kind is
            when DRecord =>

               --  For objects in record split form, we produce:
               --  let <v_name>__assume = <init_value> in
               --   <v__fields> := <v_name>__assume.fields;
               --   <v__discrs> := <v_name>__assume.discrs; if discr is mutable
               --   assume (<v__discrs> = <v_name>__assume.discrs); otherwise
               --   assume (<v__constrained>= Is_Constrained (Etype (Lvalue)));
               --   assume (<v__tag> = <v_name>__assume.tag); if classwide
               --   assume (<v__tag> = Ty.__tag); otherwise

               declare
                  Tmp_Var : constant W_Identifier_Id :=
                    New_Identifier (Name => L_Name & "__assume",
                                    Typ  => Why_Ty);
               begin
                  if Binder.Fields.Present then
                     Res := Sequence
                       (Res,
                        New_Assignment
                          (Ada_Node => N,
                           Name     => Binder.Fields.Binder.B_Name,
                           Labels   => Symbol_Sets.Empty_Set,
                           Value    => +New_Fields_Access
                             (Domain => EW_Prog,
                              Name   => +Tmp_Var,
                              Ty     => Binder.Typ),
                           Typ      =>
                             Get_Typ (Binder.Fields.Binder.B_Name)));
                  end if;

                  if Binder.Discrs.Present then
                     if Binder.Discrs.Binder.Mutable then
                        Res := Sequence
                          (Res,
                           New_Assignment
                             (Ada_Node => N,
                              Name     => Binder.Discrs.Binder.B_Name,
                              Labels   => Symbol_Sets.Empty_Set,
                              Value    => +New_Discriminants_Access
                                (Domain => EW_Prog,
                                 Name   => +Tmp_Var,
                                 Ty     => Binder.Typ),
                              Typ      =>
                                Get_Typ (Binder.Discrs.Binder.B_Name)));

                        pragma Assert (Binder.Constr.Present);
                     else
                        Res := Sequence
                          (Res,
                           New_Assume_Statement
                           (Ada_Node => N,
                            Pred     =>
                              New_Call
                                (Name => Why_Eq,
                                 Typ  => EW_Bool_Type,
                                 Args =>
                                   (1 => +Binder.Discrs.Binder.B_Name,
                                    2 =>
                                      New_Discriminants_Access
                                        (Domain => EW_Prog,
                                         Name   => +Tmp_Var,
                                         Ty     => Binder.Typ)))));
                     end if;

                     if Binder.Constr.Present then

                        Res := Sequence
                          (Res,
                           New_Assume_Statement
                           (Ada_Node => N,
                            Pred     =>
                              New_Call
                                (Name => Why_Eq,
                                 Typ => EW_Bool_Type,
                                 Args => (+Binder.Constr.Id,
                                          (if Binder.Discrs.Binder.Mutable
                                           then +False_Term
                                           else +True_Term)))));
                     end if;
                  end if;

                  if Binder.Tag.Present then
                     Res := Sequence
                       (Res,
                        New_Assume_Statement
                          (Ada_Node => N,
                           Pred     =>
                             New_Call
                               (Name => Why_Eq,
                                Typ  => EW_Bool_Type,
                                Args =>
                                  (1 => +Binder.Tag.Id,
                                   2 =>
                                     (if Is_Class_Wide_Type (Etype (Lvalue))
                                      then New_Tag_Access
                                        (Domain => EW_Prog,
                                         Name   => +Tmp_Var,
                                         Ty     => Binder.Typ)
                                      else +E_Symb (Binder.Typ, WNE_Tag))))));
                  end if;

                  return +New_Typed_Binding
                    (Ada_Node => N,
                     Domain   => EW_Prog,
                     Name     => Tmp_Var,
                     Def      => +Why_Expr,
                     Context  => +Res);
               end;

            when UCArray =>

               --  For objects in array split form, we produce:
               --  let <v_name>__assume = <init_value> in
               --    <v> := of_array (<v_name>__assume);
               --    assume (<v__first> = <v_name>__assume.first);
               --    assume (<v__last> = <v_name>__assume.last);

               declare
                  Tmp_Var : constant W_Identifier_Id :=
                    New_Identifier (Name => L_Name & "__assume",
                                    Typ  => Why_Ty);
               begin
                  Res := Sequence
                    (Res,
                     New_Assignment
                       (Ada_Node => N,
                        Name     => Binder.Content.B_Name,
                        Labels   => Symbol_Sets.Empty_Set,
                        Value    => +Array_Convert_To_Base (EW_Prog, +Tmp_Var),
                        Typ      => Get_Typ (Binder.Content.B_Name)));

                  for I in 1 .. Binder.Dim loop
                     Res := Sequence
                       ((1 => Res,
                         2 => New_Assume_Statement
                           (Ada_Node => N,
                            Pred     =>
                              New_Call
                                (Name => Why_Eq,
                                 Typ  => EW_Bool_Type,
                                 Args =>
                                   (1 => Insert_Conversion_To_Rep_No_Bool
                                      (EW_Prog,
                                       +Binder.Bounds (I).First),
                                    2 => Insert_Conversion_To_Rep_No_Bool
                                      (EW_Prog,
                                       +Get_Array_Attr
                                         (Domain => EW_Prog,
                                          Expr   => +Tmp_Var,
                                          Attr   => Attribute_First,
                                          Dim    => I))))),
                         3 => New_Assume_Statement
                           (Ada_Node => N,
                            Pred     =>
                              New_Call
                                (Name => Why_Eq,
                                 Typ  => EW_Bool_Type,
                                 Args =>
                                   (1 => Insert_Conversion_To_Rep_No_Bool
                                      (EW_Prog,
                                       +Binder.Bounds (I).Last),
                                    2 => Insert_Conversion_To_Rep_No_Bool
                                      (EW_Prog,
                                       +Get_Array_Attr
                                         (Domain => EW_Prog,
                                          Expr   => +Tmp_Var,
                                          Attr   => Attribute_Last,
                                          Dim    => I)))))));
                  end loop;

                  return +New_Typed_Binding
                    (Ada_Node => N,
                     Domain   => EW_Prog,
                     Name     => Tmp_Var,
                     Def      => +Why_Expr,
                     Context  => +Res);
               end;

            when Pointer =>

               --  For objects in access split form, we produce:
               --  let <v_name>__assume = <init_value> in
               --    <v> := <v_name>__assume.value;
               --  and either:
               --    assume (<v__addr> = <v_name>__assume.address);
               --    assume (<v__is_null> = <v_name>__assume.is_null);
               --    <v__is_moved> := false;
               --  if the pointer is not mutable, or:
               --    <v__addr> := <v_name>__assume.address;
               --    <v__is_null> := <v_name>__assume.is_null;
               --    <v__is_moved> := false;
               --  otherwise.

               declare
                  Tmp_Var : constant W_Identifier_Id :=
                    New_Identifier (Name => L_Name & "__assume",
                                    Typ  => Why_Ty);
               begin
                  Res :=
                    Sequence (Res,
                              New_Assignment
                                (Ada_Node => N,
                                 Name     => Binder.Value.B_Name,
                                 Labels   => Symbol_Sets.Empty_Set,
                                 Value    =>
                                   +New_Pointer_Value_Access
                                   (Ada_Node => Empty,
                                    Domain   => EW_Term,
                                    Name     => +Tmp_Var,
                                    E        => Etype (Lvalue)),
                                 Typ      => Get_Typ (Binder.Value.B_Name)));

                  if Binder.Mutable then
                     Res := Sequence
                       ((1 => Res,
                         2 => New_Assignment
                           (Ada_Node => N,
                            Name     => Binder.Address,
                            Labels   => Symbol_Sets.Empty_Set,
                            Value    => +New_Pointer_Address_Access
                              (E    => Etype (Lvalue),
                               Name => +Tmp_Var),
                            Typ      => EW_Int_Type),
                         3 => New_Assignment
                           (Ada_Node => N,
                            Name     => Binder.Is_Null,
                            Labels   => Symbol_Sets.Empty_Set,
                            Value    => +New_Pointer_Is_Null_Access
                              (E    => Etype (Lvalue),
                               Name => +Tmp_Var),
                            Typ      => EW_Bool_Type)));
                  else
                     Res := Sequence
                       ((1 => Res,
                         2 => New_Assume_Statement
                           (Ada_Node => N,
                            Pred     =>
                              New_Call
                                (Name => Why_Eq,
                                 Typ  => EW_Bool_Type,
                                 Args =>
                                   (1 => +Binder.Address,
                                    2 => New_Pointer_Address_Access
                                      (E    => Etype (Lvalue),
                                       Name => +Tmp_Var)))),
                         3 => New_Assume_Statement
                           (Ada_Node => N,
                            Pred     =>
                              New_Call
                                (Name => Why_Eq,
                                 Typ  => EW_Bool_Type,
                                 Args =>
                                   (1 => +Binder.Is_Null,
                                    2 => New_Pointer_Is_Null_Access
                                      (E    => Etype (Lvalue),
                                       Name => +Tmp_Var))))));
                  end if;

                  Res :=
                    Sequence (Res,
                      New_Assignment
                        (Ada_Node => N,
                         Name     => Binder.Is_Moved,
                         Labels   => Symbol_Sets.Empty_Set,
                         Value    => +False_Term,
                         Typ      => EW_Bool_Type));

                  return +New_Typed_Binding
                    (Ada_Node => N,
                     Domain   => EW_Prog,
                     Name     => Tmp_Var,
                     Def      => +Why_Expr,
                     Context  => +Res);
               end;

            when Regular
               | Concurrent_Self
            =>
               declare
                  L_Id : constant W_Identifier_Id :=
                    To_Why_Id (Lvalue, Typ => Why_Ty);
               begin
                  if Is_Mutable_In_Why (Lvalue) then

                     --  Attributes of record objects have the default values
                     --  of their type.

                     return Sequence
                       (Res,
                        New_Assignment
                          (Ada_Node => N,
                           Name     => L_Id,
                           Labels   => Symbol_Sets.Empty_Set,
                           Value    =>
                             (if Has_Record_Type (Etype (Lvalue))
                              or else Full_View_Not_In_SPARK (Etype (Lvalue))
                              then +New_Tag_Update
                                (Ada_Node => N,
                                 Domain   => EW_Prog,
                                 Name     => +Why_Expr,
                                 Ty       => Etype (Lvalue))
                              else Why_Expr),
                           Typ      => Why_Ty));

                  elsif Is_Static_Expression (Rexpr) then

                     --  We generate an ignore statement, to obtain all the
                     --  checks
                     --  ??? Is this necessary? after all, we would get a
                     --  compiler warning anyway

                     return New_Ignore (Prog => Why_Expr);

                  else
                     declare
                        Tmp_Var : constant W_Identifier_Id :=
                          New_Identifier (Name => L_Name & "__assume",
                                          Typ  => Why_Ty);
                        Eq      : constant W_Pred_Id :=
                          New_Call
                            (Name => Why_Eq,
                             Typ  => EW_Bool_Type,
                             Args => (New_Tag_Update
                                        (Ada_Node => N,
                                         Domain   => EW_Prog,
                                         Name     => +Tmp_Var,
                                         Ty       => Etype (Lvalue)),
                                      +L_Id));
                     begin
                        return +New_Typed_Binding
                          (Ada_Node => N,
                           Domain   => EW_Prog,
                           Name     => Tmp_Var,
                           Def      => +Why_Expr,
                           Context  =>
                             +New_Assume_Statement
                             (Ada_Node => N,
                              Pred     => Eq));
                     end;
                  end if;
               end;

            when Func =>
               raise Program_Error;
            end case;
         end;

      elsif not Is_Partial_View (Lvalue)
        and then not Is_Imported (Lvalue)
      then

         --  Only assume default initialization if we are in a fullview

         pragma Assert (Is_Mutable_In_Why (Lvalue));

         --  Constants cannot be default initialized

         declare
            Binder          : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, Lvalue);
            L_Deref         : constant W_Expr_Id :=
              Reconstruct_Item (Binder, Ref_Allowed => True);

            Constrained_Ty  : constant Entity_Id := Etype (Lvalue);
            --  Type of the fullview

            W_Ty            : constant W_Type_Id := Type_Of_Node (Lvalue);

            Default_Checks  : W_Prog_Id :=
              Compute_Default_Check (N, Constrained_Ty, Body_Params);
              --  Checks for runtime errors in default values

            Init_Assumption : constant W_Pred_Id :=
              Compute_Default_Init
                (Expr   => Insert_Simple_Conversion
                   (Ada_Node => Lvalue,
                    Domain   => EW_Pred,
                    Expr     => L_Deref,
                    To       => W_Ty),
                 Ty     => Constrained_Ty);
            --  Assume initial value of L

         begin
            --  Generate assumption

            if Default_Checks /= +Void then
               Default_Checks := +New_Ignore
                 (Ada_Node => Lvalue,
                  Prog     => Default_Checks);
            end if;

            --  L has its top-level constrained flag True iff its subtype is
            --  constrained.

            if Binder.Kind = DRecord and then Binder.Constr.Present then
               Default_Checks := Sequence
                   (Left  => Default_Checks,
                    Right => New_Assume_Statement
                      (Ada_Node => N,
                       Pred     =>
                         +New_Comparison
                         (Symbol => Why_Eq,
                          Left   => +Binder.Constr.Id,
                          Right  => (if Is_Constrained (Constrained_Ty)
                                     then +True_Term
                                     else +False_Term),
                          Domain => EW_Pred)));
            end if;

            --  L has its top-level initialization flag True iff its type
            --  has some initialized component.

            if Binder.Init.Present
              and then Default_Initialization
                (Constrained_Ty) /= No_Default_Initialization
            then
               Default_Checks := Sequence
                   (Left  => Default_Checks,
                    Right => New_Assignment
                      (Ada_Node => N,
                       Name     => Binder.Init.Id,
                       Labels   => Symbol_Sets.Empty_Set,
                       Value    => True_Prog,
                       Typ      => EW_Bool_Type));
            end if;

            if Init_Assumption = True_Pred then
               return Default_Checks;
            else
               return Sequence
                 (Left  => Default_Checks,
                  Right => New_Assume_Statement
                    (Ada_Node => N,
                     Pred     => Init_Assumption));
            end if;
         end;
      else
         return +Void;
      end if;
   end Assignment_Of_Obj_Decl;

   ----------------------------------
   -- Assume_Declaration_Of_Entity --
   ----------------------------------

   procedure Assume_Declaration_Of_Entity
     (E             : Entity_Id;
      Params        : Transformation_Params;
      Initialized   : Boolean;
      Top_Predicate : Boolean;
      Context       : in out W_Prog_Id)
   is
      Max_Assocs : constant Natural := 100;
      --  If the defining expression of a constant contains more than
      --  Max_Assocs N_Component_Association nodes, its definition will not be
      --  inlined.

      L_Id : constant W_Expr_Id :=
        (if Is_Protected_Type (E) then
            (if Self_Is_Mutable then
                   New_Deref (Right => Self_Name, Typ => Get_Typ (Self_Name))
              else +Self_Name)
         else Transform_Identifier (Params => Params,
                                    Expr   => E,
                                    Ent    => E,
                                    Domain => EW_Term));

   begin

      pragma Assert (L_Id /= Why_Empty);

      --  Assume dynamic property of E

      Context := Sequence
        (Context,
         Assume_Dynamic_Invariant
           (Expr          => +L_Id,
            Ty            => Etype (E),
            Initialized   => Initialized,
            Only_Var      => False,
            Top_Predicate => Top_Predicate));

      --  Assume value if constant

      if Ekind (E) = E_Constant
        or else Is_Named_Number (E)
      then
         declare
            Typ  : constant W_Type_Id := Why_Type_Of_Entity (E);
            FV   : constant Entity_Id :=
              (if Is_Object (E) and then Is_Partial_View (E)
               and then Entity_In_SPARK (Full_View (E))
               then Full_View (E) else E);
            Decl : constant Node_Id := Enclosing_Declaration (FV);
            Expr : W_Expr_Id;
         begin
            if Ekind (FV) /= E_In_Parameter
              and then Present (Expression (Decl))
              and then Entity_Comes_From_Source (Original_Node (FV))
              and then Number_Of_Assocs_In_Expression
                (Expression (Decl)) <= Max_Assocs
              and then not Contains_Volatile_Function_Call (Expression (Decl))
            then
               --  We do not issue checks here. Checks for this declaration
               --  will be issued when verifying its enclosing unit.

               Expr :=
                 +Transform_Expr (Expression (Decl),
                                  Typ,
                                  EW_Pterm,
                                  Params => Body_Params);
               declare
                  Tmp_Var : constant W_Identifier_Id :=
                    New_Temp_Identifier (Typ => Typ);
                  Eq      : constant W_Pred_Id :=
                    New_Call
                      (Name => Why_Eq,
                       Typ  => EW_Bool_Type,
                       Args =>
                         ((if Has_Record_Type (Etype (E))
                             or else Full_View_Not_In_SPARK (Etype (E))
                           then
                              New_Tag_Update
                                (Domain => EW_Prog,
                                 Name   => +Tmp_Var,
                                 Ty     => Etype (E))
                           else +Tmp_Var),
                          +L_Id));
               begin
                  if not Has_Dereference (+Expr) then
                     Context := Sequence
                       (Context,
                        +New_Typed_Binding
                          (Domain  => EW_Prog,
                           Name    => Tmp_Var,
                           Def     => +Expr,
                           Context =>
                             +New_Assume_Statement (Pred => Eq)));
                  end if;
               end;
            end if;
         end;

      --  Assume the value of 'Constrained attribute for variables with
      --  defaulted discriminants.

      elsif Ekind (E) = E_Variable then
         declare
            B  : constant Item_Type :=
                  Ada_Ent_To_Why.Element (Symbol_Table, E);
            Ty : constant Entity_Id :=
                   Get_Ada_Node (+Get_Why_Type_From_Item (B));
         begin

            if B.Kind = DRecord and then B.Constr.Present then
               Context := Sequence
                 (Context,
                  New_Assume_Statement
                    (Pred =>
                       New_Call
                         (Name => Why_Eq,
                          Typ  => EW_Bool_Type,
                          Args =>
                            (1 => +B.Constr.Id,
                             2 => (if Is_Constrained (Ty) then +True_Term
                                   else +False_Term)))));
            end if;
         end;
      end if;
   end Assume_Declaration_Of_Entity;

   ------------------------------
   -- Assume_Dynamic_Invariant --
   ------------------------------

   function Assume_Dynamic_Invariant
     (Expr          : W_Term_Id;
      Ty            : Entity_Id;
      Initialized   : Boolean := True;
      Only_Var      : Boolean := True;
      Top_Predicate : Boolean := True;
      Use_Pred      : Boolean := True) return W_Prog_Id
   is
      Init     : constant W_Term_Id :=
        (if Initialized then True_Term else False_Term);
      O_Var    : constant W_Term_Id :=
        (if Only_Var then True_Term else False_Term);
      Top_Pred : constant W_Term_Id :=
        (if Top_Predicate then True_Term else False_Term);
      T        : constant W_Pred_Id :=
        Compute_Dynamic_Invariant (Expr          => Expr,
                                   Ty            => Ty,
                                   Initialized   => Init,
                                   Only_Var      => O_Var,
                                   Top_Predicate => Top_Pred,
                                   Use_Pred      => Use_Pred,
                                   Params        => Body_Params);
   begin
      if T /= True_Pred then
         return New_Assume_Statement (Ada_Node => Ty,
                                      Pred     => T);
      else
         return +Void;
      end if;
   end Assume_Dynamic_Invariant;

   --------------------------------------------
   -- Assume_Dynamic_Invariant_For_Variables --
   --------------------------------------------

   function Assume_Dynamic_Invariant_For_Variables
     (Vars             : Node_Sets.Set;
      Params           : Transformation_Params;
      Scope            : Entity_Id := Empty;
      Exclude_Top_Pred : Entity_Id := Empty;
      Initialized      : Boolean   := False) return W_Prog_Id
   is
      Dynamic_Prop_Inputs : W_Prog_Id := +Void;
      Includes            : Node_Sets.Set := Vars;
      Already_Included    : Node_Sets.Set := Node_Sets.Empty_Set;
      Prop_For_Include    : W_Prog_Id;
      Top_Predicate       : Boolean;
      First_Iter          : Boolean := True;
      Variables           : Flow_Id_Sets.Set;
      --  Set of variable inputs used in the assumed dynamic invariants.
      --  We will also need to assume their dynamic invariant.

   begin
      while not Node_Sets.Is_Empty (Includes) loop
         Prop_For_Include := +Void;
         Flow_Id_Sets.Clear (Variables);
         for Obj of Includes loop

            --  The self reference of a protected subprogram is always
            --  initialized. We only consider protected types in first
            --  iteration. Indeed, later, they will have been added by
            --  Compute_Ada_Node_Set and won't be relevant.

            if First_Iter and then Is_Protected_Type (Obj) then

               Assume_Declaration_Of_Entity
                 (E             => Obj,
                  Params        => Params,
                  Initialized   => True,
                  Top_Predicate => True,
                  Context       => Prop_For_Include);

            --  No need to assume anything if Obj is not an object, if it is
            --  not in SPARK or if it is a local object of the unit.

            elsif not (Is_Object (Obj) or else Is_Named_Number (Obj))
              or else not Ada_Ent_To_Why.Has_Element (Symbol_Table, Obj)
              or else (Present (Scope)
                       and then Is_Declared_In_Unit (Obj, Scope))
            then
               null;
            else
               --  If Obj is the parameter of a predicate function, do not
               --  assume the toplevel predicate for checking absence of RTE
               --  in the predicate function itself.

               Top_Predicate := Exclude_Top_Pred /= Obj;

               Assume_Declaration_Of_Entity
                 (E             => Obj,
                  Params        => Params,
                  Initialized   =>
                    (if Is_Object (Obj)
                       and then Is_Mutable_In_Why (Obj)
                       and then not Initialized
                     then Is_Initialized_In_Scope (Obj, Scope)
                     else True),
                  Top_Predicate => Top_Predicate,
                  Context       => Prop_For_Include);

               --  Add all the variable inputs of the dynamic invariant
               --  to the set of variables to consider.

               Variables_In_Dynamic_Invariant (Etype (Obj), Variables);
            end if;
         end loop;

         Dynamic_Prop_Inputs := Sequence
           (Prop_For_Include, Dynamic_Prop_Inputs);
         Node_Sets.Union (Already_Included, Includes);
         Includes := Compute_Ada_Node_Set (+Prop_For_Include);

         --  Add the variable inputs of dynamic predicates to Includes so
         --  that their dynamic invariant can be assumed.

         for Var of Variables loop
            case Var.Kind is
               when Direct_Mapping =>
                  Node_Sets.Include (Includes, Get_Direct_Mapping_Id (Var));

               when Magic_String =>
                  pragma Assert (Is_Opaque_For_Proof (Var));

               when others =>
                  raise Program_Error;
            end case;
         end loop;

         Node_Sets.Difference (Includes, Already_Included);
         First_Iter := False;
      end loop;
      return Dynamic_Prop_Inputs;
   end Assume_Dynamic_Invariant_For_Variables;

   -------------------------------
   -- Assume_Value_Of_Constants --
   -------------------------------

   procedure Assume_Value_Of_Constants
     (Why_Expr : in out W_Prog_Id;
      Scope    : Entity_Id;
      Params   : Transformation_Params)
   is
      Include : constant Node_Sets.Set := Compute_Ada_Node_Set (+Why_Expr);
      Assumes : W_Prog_Id := +Void;
   begin
      for N of Include loop
         if Nkind (N) in N_Entity
           and then
             ((Ekind (N) = E_Constant
               and then not Has_Variable_Input (N)
               and then not Is_Declared_In_Unit (N, Scope))

              --  We only consider here parameters of enclosing subprograms.
              --  Parameters of Scope are handled specifically.

              or else (Ekind (N) = E_In_Parameter
                       and then Enclosing_Unit (N) /= Scope))
         then
            Assume_Declaration_Of_Entity
              (E             => N,
               Params        => Params,
               Initialized   => True,
               Top_Predicate => True,
               Context       => Assumes);
         end if;
      end loop;
      Why_Expr := Sequence (Assumes, Why_Expr);
   end Assume_Value_Of_Constants;

   -------------------------------
   -- Bind_From_Mapping_In_Expr --
   -------------------------------

   function Bind_From_Mapping_In_Expr
     (Params                 : Transformation_Params;
      Map                    : Ada_To_Why_Ident.Map;
      Expr                   : W_Prog_Id;
      Guard_Map              : Ada_To_Why_Ident.Map :=
        Ada_To_Why_Ident.Empty_Map;
      Others_Guard_Ident     : W_Identifier_Id := Why_Empty;
      Do_Runtime_Error_Check : Boolean := True;
      Bind_Value_Of_Old      : Boolean := False) return W_Prog_Id
   is
      function Get_Corresponding_Guard (N : Node_Id) return Node_Id;
      --  If N is inside the consequence expression of a contract case, return
      --  the corresponding guard expression. Otherwise, return Empty.

      -----------------------------
      -- Get_Corresponding_Guard --
      -----------------------------

      function Get_Corresponding_Guard (N : Node_Id) return Node_Id is

         function Is_Pragma (N : Node_Id) return Boolean is
           (Nkind (N) = N_Pragma);
         --  @param N any Node
         --  @return True if N is a pragma.

         function Enclosing_Pragma is new
           First_Parent_With_Property (Is_Pragma);

         P : Node_Id;

      begin
         --  Retrieve the enclosing pragma, which may be either a postcondition
         --  or a contract_cases pragma.

         P := Enclosing_Pragma (N);

         --  Return Empty for a postcondition pragma

         if Is_Pragma_Check (P, Name_Post)
              or else
            Is_Pragma_Check (P, Name_Postcondition)
              or else
            Is_Pragma_Check (P, Name_Refined_Post)
              or else
            Is_Pragma (P, Pragma_Post)
              or else
            Is_Pragma (P, Pragma_Postcondition)
              or else
            Is_Pragma (P, Pragma_Refined_Post)
         then
            return Empty;
         end if;

         pragma Assert (Is_Pragma (P, Pragma_Contract_Cases));

         --  Retrieve the enclosing contract case component_association

         declare
            All_Cases : constant List_Id :=
              Component_Associations
                (Get_Pragma_Arg (First (Pragma_Argument_Associations (P))));

            function Is_Contract_Case (N : Node_Id) return Boolean is
              (Is_List_Member (N) and then List_Containing (N) = All_Cases);
            --  @param N any Node
            --  @return True if N is a an element of All_Cases.

            function Enclosing_Contract_Case is new
              First_Parent_With_Property (Is_Contract_Case);

         begin
            P := Enclosing_Contract_Case (N);
         end;

         pragma Assert (Nkind (P) = N_Component_Association);

         --  Return the guard of the enclosing contract case

         return First (Choices (P));
      end Get_Corresponding_Guard;

      Result : W_Prog_Id := Expr;

   --  Start of processing for Bind_From_Mapping_In_Expr

   begin
      for C in Map.Iterate loop
         declare
            N     : constant Node_Id := Ada_To_Why_Ident.Key (C);
            Name  : constant W_Identifier_Id := Ada_To_Why_Ident.Element (C);
            Guard : constant Node_Id :=
              (if Bind_Value_Of_Old
               then Get_Corresponding_Guard (N)
               else Empty);

            --  Generate a program expression to check absence of run-time
            --  errors. When checking for X in X'Old inside a contract case
            --  (which corresponds to Guard being non Empty), do this checking
            --  only under a condition that the corresponding case is enabled.

            RE_Prog : constant W_Prog_Id :=
              (if Do_Runtime_Error_Check then
                (if Present (Guard) then
                  New_Conditional
                    (Condition =>
                       +(if Nkind (Guard) = N_Others_Choice then
                           Others_Guard_Ident
                         else
                           Guard_Map.Element (Guard)),
                     Then_Part => +New_Ignore
                       (Prog => +Transform_Expr_Or_Identifier
                            (N, EW_Prog, Params)))
                 else
                     New_Ignore (Prog => +Transform_Expr_Or_Identifier
                                 (N, EW_Prog, Params)))
               else
                 +Void);

            --  Generate a term definition for the value of the object at
            --  subprogram entry, and link with rest of code. This
            --  definition does not involve lazy boolean operators, so it
            --  does not lead to more paths being generated in the naive WP,
            --  contrary to what we would get if directly defining the value
            --  of the object as a program. This is particularly useful for
            --  guards of Contract_Cases.

            Let_Prog : constant W_Prog_Id :=
              +New_Typed_Binding
                (Name   => Name,
                 Domain => EW_Prog,
                 Def    =>
                   +New_Simpl_Any_Prog
                   (T    => Get_Typ (Name),
                    Pred =>
                      New_Call
                        (Name   => Why_Eq,
                         Typ    => EW_Bool_Type,
                         Args =>
                           (1 => +New_Result_Ident (Get_Typ (Name)),
                            2 => +Insert_Simple_Conversion
                              (Domain         => EW_Term,
                               Expr           => Transform_Expr_Or_Identifier
                                 (N, EW_Term, Params),
                               To             => Get_Typ (Name),
                               Force_No_Slide => True)))),
                 Context => +Result);
         begin
            Result := Sequence (RE_Prog, Let_Prog);
         end;
      end loop;

      return Result;
   end Bind_From_Mapping_In_Expr;

   ---------------------------
   -- Case_Expr_Of_Ada_Node --
   ---------------------------

   function Case_Expr_Of_Ada_Node
     (N             : Node_Id;
      Expected_Type : W_Type_OId := Why_Empty;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id
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
      --  We generate a single if expression, with a list of elsif cases, to
      --  avoid the generation of deep Why3 expressions, which may lead to
      --  stack overflow when traversing recursively the expression:
      --
      --    if X = Case_1 then S1
      --    elsif ...
      --    elsif X = Case_N then Sn
      --    else S

      function Branch_Expr (N : Node_Id) return W_Expr_Id;
      --  Return the expression that corresponds to a branch; decide which
      --  function to call depending on the type of the branch.

      -----------------
      -- Branch_Expr --
      -----------------

      function Branch_Expr (N : Node_Id) return W_Expr_Id is
         T : W_Expr_Id;

      begin
         case Nkind (N) is
            when N_Case_Expression_Alternative =>
               Ada_Ent_To_Why.Push_Scope (Symbol_Table);
               if Present (Actions (N)) then
                  Transform_Actions_Preparation (Actions (N));
               end if;

               if Expected_Type = Why_Empty then
                  T := Transform_Expr (Expression (N),
                                       Domain,
                                       Params);
               else
                  T := Transform_Expr (Expression (N),
                                       Expected_Type,
                                       Domain,
                                       Params);
               end if;

               if Present (Actions (N)) then
                  T := Transform_Actions (Actions (N),
                                          T,
                                          Domain,
                                          Params);
               end if;
               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

               --  Possibly warn on an unreachable case branch

               if Domain = EW_Prog then
                  T := Warn_On_Dead_Branch (Expression (N), T, Params.Phase);
               end if;

               return T;

            when N_Case_Statement_Alternative =>
               --  ??? Maybe we should merge the code for statements?
               T := +Transform_Statements_And_Declarations (Statements (N));

               --  Possibly warn on dead code

               T :=
                 +Warn_On_Dead_Code (First (Statements (N)), +T, Params.Phase);

               return T;

            when others =>
               raise Unexpected_Node;
         end case;
      end Branch_Expr;

      Match_Domain : constant EW_Domain :=
         (if Domain = EW_Pred then EW_Term else Domain);
      Cond_Domain  : constant EW_Domain :=
        (if Domain = EW_Term then EW_Pred
         elsif Domain = EW_Prog then EW_Pterm
         else Domain);
      --  As the choices must be static, we do not need to generate checks
      --  for them.

      Cases        : constant List_Id := Alternatives (N);
      First_Case   : constant Node_Id := First (Cases);
      Last_Case    : constant Node_Id := Last (Cases);
      Expr         : constant Node_Id := Expression (N);
      Cur_Case     : Node_Id;
      Matched_Expr : constant W_Expr_Id :=
                       Transform_Expr (Expr,
                                       Base_Why_Type_No_Bool
                                         (Entity_Id'(Type_Of_Node (Expr))),
                                       Match_Domain,
                                       Params);
      Then_Expr    : constant W_Expr_Id := Branch_Expr (First_Case);
      Elsif_Parts  : W_Expr_Array (1 .. Integer (List_Length (Cases)) - 2);

   --  Start of processing for Case_Expr_Of_Ada_Node

   begin
      if List_Length (Cases) = 1 then
         return Then_Expr;

      else
         Cur_Case := Next (First_Case);
         for Offset in 1 .. List_Length (Cases) - 2 loop
            declare
               Disc_Choices : constant W_Expr_Id :=
                 Transform_Discrete_Choices
                   (Choices      => Discrete_Choices (Cur_Case),
                    Choice_Type  => Empty,
                    Matched_Expr => Matched_Expr,
                    Cond_Domain  => Cond_Domain,
                    Params       => Params);
            begin
               Elsif_Parts (Integer (Offset)) :=
                 New_Elsif
                   (Domain    => Domain,
                    Condition =>
                      (if Nkind (N) in N_Case_Statement then
                         New_Counterexample_Assign
                           (If_Node   => Cur_Case,
                            Condition => Disc_Choices)
                       else
                          Disc_Choices),
                 Then_Part => Branch_Expr (Cur_Case));
               Next (Cur_Case);
            end;
         end loop;

         declare
            Disc_Choices : constant W_Expr_Id :=
              Transform_Discrete_Choices
                (Choices      => Discrete_Choices (First_Case),
                 Choice_Type  => Empty,
                 Matched_Expr => Matched_Expr,
                 Cond_Domain  => Cond_Domain,
                 Params       => Params);
         begin
            return New_Conditional
              (Domain      => Domain,
               Condition   =>
                 (if Nkind (N) in N_Case_Statement then
                    New_Counterexample_Assign
                      (If_Node   => First_Case,
                       Condition => Disc_Choices)
                  else
                     Disc_Choices),

               Then_Part   => Then_Expr,
               Elsif_Parts => Elsif_Parts,
               Else_Part   => Branch_Expr (Last_Case),
               Typ         => Get_Type (Then_Expr));
         end;
      end if;
   end Case_Expr_Of_Ada_Node;

   ---------------------------
   -- Check_No_Memory_Leaks --
   ---------------------------

   function Check_No_Memory_Leaks
     (Ada_Node           : Node_Id;
      N                  : Node_Or_Entity_Id;
      Is_Uncheck_Dealloc : Boolean := False;
      At_End_Of_Scope    : Boolean := False)
      return W_Prog_Id
   is
      Init_Typ : constant Entity_Id := Retysp (Etype (N));

      --  For Unchecked_Deallocation, we are not interested in the access type
      --  itself, but in the designated type. The fact that the argument of
      --  Unchecked_Deallocation should not be moved is checked already by the
      --  borrow checker. Here we check that all pointers in the designated
      --  value, if any, are moved (null being a special case of moved).

      Typ      : constant Entity_Id :=
        (if Is_Uncheck_Dealloc then
           Retysp (Directly_Designated_Type (Init_Typ))
         else Init_Typ);

      Result   : W_Prog_Id := +Void;
      Kind     : constant VC_Kind :=
        (if At_End_Of_Scope then
            VC_Memory_Leak_At_End_Of_Scope
         else
            VC_Memory_Leak);

   begin
      --  Nothing to check on borrow/observe of anonymous access type

      if Is_Deep (Typ)
        and then not Is_Anonymous_Access_Type (Typ)
      then
         declare
            Val      : constant W_Expr_Id :=
              Transform_Expr_Or_Identifier (N, EW_Pterm, Body_Params);
            Tmp      : constant W_Expr_Id := New_Temp_For_Expr (Val);
            Is_Moved : constant W_Pred_Id :=
              (if Is_Uncheck_Dealloc then
                 New_Conditional
                   (Condition => New_Comparison
                      (Symbol => Why_Eq,
                       Left   => New_Pointer_Is_Null_Access (Init_Typ, Tmp),
                       Right  => +False_Term,
                       Domain => EW_Pred),
                    Then_Part =>
                      +Compute_Is_Moved_Property
                        (+New_Pointer_Value_Access
                           (Ada_Node => Empty,
                            E        => Init_Typ,
                            Name     => +Tmp,
                            Domain   => EW_Term), Typ),
                    Typ       => EW_Bool_Type)
               else
                 Compute_Is_Moved_Property (+Tmp, Typ));

            --  As memory leaks do not lead to runtime errors, it is possible
            --  that these messages get ignored or even justified by users
            --  in some cases. Thus, it is particularly important that the
            --  corresponding checks have no effect on the rest of analysis,
            --  which we obtain here by enclosing the check in an ignore block.

            Check   : constant W_Expr_Id :=
              +New_Ignore (Prog =>
                 New_Located_Assert (Ada_Node,
                   Is_Moved,
                   Kind,
                   EW_Assert));
         begin
            Result := +Binding_For_Temp (Domain  => EW_Prog,
                                         Tmp     => Tmp,
                                         Context => Check);
         end;
      end if;

      return Result;
   end Check_No_Memory_Leaks;

   -------------------------------------------
   -- Check_No_Memory_Leaks_At_End_Of_Scope --
   -------------------------------------------

   function Check_No_Memory_Leaks_At_End_Of_Scope
     (Decls : List_Id) return W_Prog_Id
   is
      Cur_Decl : Node_Id := First (Decls);
      Result   : W_Statement_Sequence_Id := Void_Sequence;

   begin
      while Present (Cur_Decl) loop
         case Nkind (Cur_Decl) is

            --  Only consider objects in SPARK, so that parts of packages
            --  marked SPARK_Mode Off are ignored.

            when N_Object_Declaration =>
               if Entity_In_SPARK (Defining_Identifier (Cur_Decl)) then
                  Sequence_Append (Result,
                    Check_No_Memory_Leaks
                      (Cur_Decl, Defining_Identifier (Cur_Decl),
                       At_End_Of_Scope => True));
               end if;

            --  Objects in local packages should be deallocated before
            --  returning from the enclosing subprogram.

            when N_Package_Declaration =>
               declare
                  Pack : constant Entity_Id :=
                    Unique_Defining_Entity (Cur_Decl);
               begin
                  Sequence_Append (Result,
                    Check_No_Memory_Leaks_At_End_Of_Scope
                      (Visible_Declarations_Of_Package (Pack)));
                  Sequence_Append (Result,
                    Check_No_Memory_Leaks_At_End_Of_Scope
                      (Private_Declarations_Of_Package (Pack)));
               end;

            when N_Package_Body =>
               Sequence_Append (Result,
                 Check_No_Memory_Leaks_At_End_Of_Scope
                   (Declarations (Cur_Decl)));

            when others =>
               null;
         end case;
         Next (Cur_Decl);
      end loop;

      return +Result;
   end Check_No_Memory_Leaks_At_End_Of_Scope;

   --------------------------------------------
   -- Check_No_Wrap_Around_Modular_Operation --
   --------------------------------------------

   function Check_No_Wrap_Around_Modular_Operation
     (Ada_Node   : Node_Id;
      Ada_Type   : Entity_Id;
      Op         : N_Op;
      Left_Opnd  : W_Expr_Id := Why_Empty;
      Right_Opnd : W_Expr_Id;
      Rep_Type   : W_Type_Id;
      Modulus    : Uint) return W_Prog_Id
   is
   begin
      --  Negation of a modular value does not overflow iff the value is zero

      if Op = N_Op_Minus then
         declare
            Right_Expr : constant W_Expr_Id := New_Temp_For_Expr (Right_Opnd);
            Zero_Expr  : constant W_Expr_Id :=
              New_Modular_Constant (Value => Uint_0,
                                    Typ   => Rep_Type);
            Check : W_Expr_Id;
         begin
            Check := +New_Comparison (Symbol => Why_Eq,
                                      Left   => Right_Expr,
                                      Right  => Zero_Expr,
                                      Domain => EW_Pred);
            Check := +New_Ignore (Prog =>
                                   New_Located_Assert (Ada_Node,
                                     +Check,
                                     VC_Overflow_Check,
                                     EW_Assert));
            return +Binding_For_Temp (Domain  => EW_Prog,
                                      Tmp     => Right_Expr,
                                      Context => Check);
         end;

      --  For binary operations, go to a suitably large bitvector for computing
      --  the result, then check it is strictly lower than the modulus.

      else
         declare
            Left_Expr  : constant W_Expr_Id := New_Temp_For_Expr (Left_Opnd);
            Right_Expr : constant W_Expr_Id := New_Temp_For_Expr (Right_Opnd);

            Next_Bv      : constant W_Type_Id :=
              (if Modulus <= UI_Expon (2, 8) then
                 (if Modular_Size (Ada_Type) < 16 then EW_BitVector_16_Type
                  else Rep_Type)
               elsif Modulus <= UI_Expon (2, 16) then
                 (if Modular_Size (Ada_Type) < 32 then EW_BitVector_32_Type
                  else Rep_Type)
               elsif Modulus <= UI_Expon (2, 32) then
                 (if Modular_Size (Ada_Type) < 64 then EW_BitVector_64_Type
                  else Rep_Type)
               else
                  EW_BitVector_128_Type);
            Modulus_Expr : constant W_Expr_Id :=
              New_Modular_Constant (Value => Modulus,
                                    Typ   => Next_Bv);
            Next_Left    : constant W_Expr_Id :=
              Insert_Simple_Conversion (Domain => EW_Term,
                                        Expr   => Left_Expr,
                                        To     => Next_Bv);
            Next_Right   : constant W_Expr_Id :=
              Insert_Simple_Conversion (Domain => EW_Term,
                                        Expr   => Right_Expr,
                                        To     => Next_Bv);
            Oper         : constant W_Identifier_Id :=
              (case Op is
                 when N_Op_Add      => MF_BVs (Next_Bv).Add,
                 when N_Op_Subtract => MF_BVs (Next_Bv).Sub,
                 when N_Op_Multiply => MF_BVs (Next_Bv).Mult,
                 when others        => raise Program_Error);
            Oper_Expr     : constant W_Expr_Id :=
              New_Call (Ada_Node => Ada_Node,
                        Domain   => EW_Term,
                        Name     => Oper,
                        Args     => (1 => Next_Left,
                                     2 => Next_Right),
                        Typ      => Next_Bv);
            Check : W_Expr_Id;
         begin
            Check := +New_Comparison (Symbol => MF_BVs (Next_Bv).Ult,
                                      Left   => Oper_Expr,
                                      Right  => Modulus_Expr,
                                      Domain => EW_Pred);
            Check := +New_Ignore (Prog =>
                                   New_Located_Assert (Ada_Node,
                                     +Check,
                                     VC_Overflow_Check,
                                     EW_Assert));
            Check := Binding_For_Temp (Domain  => EW_Prog,
                                       Tmp     => Right_Expr,
                                       Context => Check);
            return +Binding_For_Temp (Domain  => EW_Prog,
                                      Tmp     => Left_Expr,
                                      Context => Check);
         end;
      end if;
   end Check_No_Wrap_Around_Modular_Operation;

   -------------------------
   -- Check_Type_With_DIC --
   -------------------------

   function Check_Type_With_DIC
     (Params : Transformation_Params;
      N      : Entity_Id) return W_Prog_Id
   is
      Ty        : constant Entity_Id := Retysp (N);

      DIC_Subp  : constant Entity_Id := DIC_Procedure (N);
      DIC_Expr  : constant Node_Id := Get_Expr_From_Check_Only_Proc (DIC_Subp);
      DIC_Param : constant Entity_Id := First_Formal (DIC_Subp);
      DIC_Check : W_Prog_Id := +Void;

   begin
      --  Generate let x = any Ty
      --               {Default_Init (result) /\ Dynamic_Invariant (result)} in
      --        ignore__ (Def_Init_Cond (x));
      --        assert {Def_Init_Cond (x)}

      if Present (DIC_Expr) then

         --  Add the binder for the reference to the type to the
         --  Symbol_Table.

         Ada_Ent_To_Why.Push_Scope (Symbol_Table);

         declare
            Tmp_Id   : constant W_Identifier_Id :=
              New_Temp_Identifier (Ty, Type_Of_Node (Ty));
            Tmp_Post : constant W_Pred_Id :=
              +New_And_Then_Expr
              (Left   =>
                 +Compute_Dynamic_Invariant
                 (Expr        => +New_Result_Ident (Type_Of_Node (Ty)),
                  Ty          => Ty,
                  Initialized => True_Term,
                  Only_Var    => False_Term,
                  Params      => Params),
               Right  =>
                 +Compute_Default_Init
                 (Expr             => +New_Result_Ident (Type_Of_Node (Ty)),
                  Ty               => Ty,
                  Include_Subtypes => True,
                  Skip_Last_Cond   => True_Term),
               Domain => EW_Pred);
            --  Assume default initialization of the expression. Do not assume
            --  the DIC itself.

            Tmp_Def : constant W_Prog_Id :=
              New_Any_Expr (Ada_Node    => N,
                            Post        => Tmp_Post,
                            Labels      => Symbol_Sets.Empty_Set,
                            Return_Type => Type_Of_Node (Ty));

         begin
            --  Store the entity for the type variable

            Insert_Entity (DIC_Param, Tmp_Id);

            DIC_Check := Sequence
              (New_Ignore
                 (Prog     => +Transform_Expr
                      (Expr    => DIC_Expr,
                       Domain  => EW_Prog,
                       Params  => Params)),
               New_Located_Assert
                 (Ada_Node =>
                      (if Is_Full_View (N) then Partial_View (N) else N),
                  Kind     => EW_Check,
                  Reason   => VC_Default_Initial_Condition,
                  Pred     => +Transform_Expr
                    (Expr    => DIC_Expr,
                     Domain  => EW_Pred,
                     Params  => Params)));

            DIC_Check := +New_Typed_Binding
              (Domain  => EW_Prog,
               Name    => Tmp_Id,
               Def     => +Tmp_Def,
               Context => +DIC_Check);

            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         end;
      end if;
      return DIC_Check;
   end Check_Type_With_DIC;

   ---------------------------------
   --  Check_Type_With_Invariants --
   ---------------------------------

   function Check_Type_With_Invariants
     (Params : Transformation_Params;
      N      : Entity_Id) return W_Prog_Id
   is
      Ty      : constant Entity_Id := Retysp (N);
      Base_Ty : constant Entity_Id := Base_Type (Ty);
      --  For first subtypes, we generate a check if the base type has an
      --  invariant.

      Tmp_Id    : constant W_Identifier_Id :=
        New_Temp_Identifier (Ty, Type_Of_Node (Ty));
      Tmp_Post  : constant W_Pred_Id :=
        Compute_Dynamic_Invariant
          (Expr        => +New_Result_Ident (Type_Of_Node (Ty)),
           Ty          => Ty,
           Initialized => True_Term,
           Only_Var    => False_Term,
           Params      => Params);
      Tmp_Def   : constant W_Prog_Id :=
        New_Any_Expr (Ada_Node    => N,
                      Post        => Tmp_Post,
                      Labels      => Symbol_Sets.Empty_Set,
                      Return_Type => Type_Of_Node (Ty));

      Inv_RTE   : W_Prog_Id;
      Inv_Check : W_Prog_Id;

   begin
      --  Generate:
      --  let tmp = any Ty ensure {dynamic_invariant (result)} in
      --  ignore (inv_expr (tmp));  -- only if Ty has an invariant
      --  assume {default_init (tmp)};
      --  assert {inv_expr (tmp)}

      --  If the type itself has an invariant, check for runtime errors in the
      --  type's invariant.

      if Has_Invariants_In_SPARK (Base_Ty) then
         declare
            Inv_Subp  : constant Node_Id := Invariant_Procedure (Ty);
            Inv_Expr  : constant Node_Id :=
              Get_Expr_From_Check_Only_Proc (Inv_Subp);
            Inv_Param : constant Entity_Id := First_Formal (Inv_Subp);
         begin
            Ada_Ent_To_Why.Push_Scope (Symbol_Table);
            Insert_Entity (Inv_Param, Tmp_Id);
            Inv_RTE :=
              +Transform_Expr (Expr          => Inv_Expr,
                               Expected_Type => EW_Bool_Type,
                               Domain        => EW_Prog,
                               Params        => Params);
            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

            Inv_RTE := New_Ignore (Inv_Expr, Inv_RTE);
         end;
      else
         Inv_RTE := +Void;
      end if;

      --  Check that the default values of the type and all its subtypes
      --  respect its invariant.

      Inv_Check :=
        +Sequence
        (Left  => New_Assume_Statement
           (Ty, Compute_Default_Init
                (+Tmp_Id, N, Params, Include_Subtypes => True,
                 Skip_Last_Cond =>
                   (if Has_DIC (Ty) and then Needs_DIC_Check_At_Use (Ty)
                    then False_Term else True_Term))),
         Right => New_Invariant_Check (N, Ty, +Tmp_Id, True));

      return New_Ignore (Ty,
                         +New_Typed_Binding
                           (Domain  => EW_Prog,
                            Name    => Tmp_Id,
                            Def     => +Tmp_Def,
                            Context => +Sequence (Inv_RTE, Inv_Check)));
   end Check_Type_With_Invariants;

   ------------------------
   -- Check_Scalar_Range --
   ------------------------

   function Check_Scalar_Range
     (Params : Transformation_Params;
      N      : Entity_Id;
      Base   : Entity_Id) return W_Prog_Id
   is
      Rng  : constant Node_Id := Get_Range (N);
      Low  : constant Node_Id := Low_Bound (Rng);
      High : constant Node_Id := High_Bound (Rng);

   begin
      --  If the range is static, raises no run-time errors by itself, and no
      --  base type is passed, there is nothing to do.

      if Is_OK_Static_Range (Rng)
        and then No (Base)
      then
         return +Void;

      --  If the range is static, raises no run-time errors by itself, and a
      --  base type is passed, we need to check that either the range is empty
      --  or the bounds fit in the base type. Do nothing when either of these
      --  conditions can be verified statically.

      elsif Is_OK_Static_Range (Rng)
        and then Present (Base)
        and then Has_Static_Scalar_Subtype (Base)
        and then
          ((if Is_Floating_Point_Type (Base) then
              Expr_Value_R (High) < Expr_Value_R (Low)
            else
              Expr_Value (High) < Expr_Value (Low))
        or else
          (Is_In_Range (N   => Low,
                        Typ => Base)
             and then
           Is_In_Range (N   => High,
                        Typ => Base)))
      then
         return +Void;

      else
         pragma Assert (Present (Base));
         declare
            Why_Base         : constant W_Type_Id :=
              Base_Why_Type_No_Bool (Base);
            Le               : constant W_Identifier_Id :=
              (if Why_Type_Is_Float (Why_Base) then
                    MF_Floats (Why_Base).Le
               elsif Why_Type_Is_BitVector (Why_Base) then
                    MF_BVs (Why_Base).Ule
               else Int_Infix_Le);
            Low_Expr         : constant W_Term_Id :=
              +Transform_Expr (Low, Why_Base, EW_Term, Params);
            High_Expr        : constant W_Term_Id :=
              +Transform_Expr (High, Why_Base, EW_Term, Params);
            First_In_Range   : constant W_Pred_Id :=
              New_Call
                (Name =>
                   (if Why_Type_Is_Float (Why_Base) then
                         MF_Floats (Why_Base).Ge
                    elsif Why_Type_Is_BitVector (Why_Base) then
                         MF_BVs (Why_Base).Uge
                    else Int_Infix_Ge),
                 Typ  => EW_Bool_Type,
                 Args => (+Low_Expr,
                          +New_Attribute_Expr
                            (Base, EW_Term, Attribute_First, Params)));
            Last_In_Range    : constant W_Pred_Id :=
              New_Call
                (Name => Le,
                 Typ  => EW_Bool_Type,
                 Args => (+High_Expr,
                             +New_Attribute_Expr
                               (Base, EW_Term, Attribute_Last, Params)));
            First_Le_Last    : constant W_Pred_Id :=
              New_Call
                (Name => Le,
                 Typ  => EW_Bool_Type,
                 Args => (+Low_Expr, +High_Expr));
            Precond          : constant W_Pred_Id :=
              +New_Connection
              (Op     => EW_Imply,
               Left   => +First_Le_Last,
               Right  =>
                 +New_And_Expr
                 (Domain => EW_Pred,
                  Left   => +First_In_Range,
                  Right => +Last_In_Range));

            Check_Range      : W_Prog_Id;
         begin

            --  We need to check both that the range is OK (either
            --  empty or contained in the range's type) and that there cannot
            --  be any runtime errors during the computation of the bounds.
            --  If the range bounds where computed by the frontend, we assume
            --  that they are correct.

            Check_Range :=
              +New_Any_Statement (Ada_Node => N,
                                  Pre      => Precond,
                                  Reason   => VC_Range_Check,
                                  Post     => True_Pred);

            if Comes_From_Source (Original_Node (Low))
              and then not Is_OK_Static_Expression (Low)
            then
               Check_Range := Sequence
                 (New_Ignore
                    (Ada_Node => N,
                     Prog     => +Transform_Expr
                       (Low, Why_Base, EW_Prog, Params)),
                  Check_Range);
            end if;

            if Comes_From_Source (Original_Node (High))
              and then not Is_OK_Static_Expression (High)
            then
               Check_Range := Sequence
                 (New_Ignore
                    (Ada_Node => N,
                     Prog     => +Transform_Expr
                       (High, Why_Base, EW_Prog, Params)),
                  Check_Range);
            end if;

            return Check_Range;
         end;
      end if;
   end Check_Scalar_Range;

   ------------------------------
   -- Check_Subtype_Indication --
   ------------------------------

   function Check_Subtype_Indication
     (Params   : Transformation_Params;
      N        : Node_Id;
      Sub_Type : Entity_Id) return W_Prog_Id is
   begin
      if Is_Scalar_Type (Sub_Type) then
         return Check_Scalar_Range (Params   => Params,
                                    N        => Sub_Type,
                                    Base     => Etype (Subtype_Mark (N)));
      else
         return +Void;
      end if;
   end Check_Subtype_Indication;

   -----------------------------------
   -- Compute_Assumption_For_Borrow --
   -----------------------------------

   function Compute_Assumption_For_Borrow
     (Brower      : Entity_Id;
      Borrowed_Id : W_Identifier_Id;
      Params      : Transformation_Params) return W_Pred_Id
   is
      Borrowed : constant Entity_Id := Get_Borrowed_Entity (Brower);

      function Path_From_Name (Path : Node_Id) return W_Expr_Id;
      --  Compute Borrowed_Id.Path if Path is a path rooted at Borrowed

      function Path_From_Name (Path : Node_Id) return W_Expr_Id is
         W_Expr : W_Expr_Id;
      begin
         Ada_Ent_To_Why.Push_Scope (Symbol_Table);
         Insert_Entity (Borrowed, Borrowed_Id);
         W_Expr := Transform_Expr
           (Expr    => Path,
            Domain  => EW_Term,
            Params  => Params);
         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         return W_Expr;
      end Path_From_Name;

      Res : W_Pred_Id := True_Pred;
      Cur : Node_Id;

   begin
      --  For traversal functions, the whole parameter is borrowed. We only
      --  preserve the is_null field of the borrowed object.
      --  ??? We could also state that the address is preserved.

      if Ekind (Brower) = E_Function then
         declare
            Ty : constant Entity_Id := Retysp (Etype (Borrowed));
         begin
            return
              +New_Comparison
                (Symbol => Why_Eq,
                 Left   => New_Pointer_Is_Null_Access
                   (Ty, Transform_Identifier
                      (Params   => Params,
                       Expr     => Borrowed,
                       Ent      => Borrowed,
                       Domain   => EW_Term)),
                 Right  => New_Pointer_Is_Null_Access (Ty, +Borrowed_Id),
                 Domain => EW_Pred);
         end;
      end if;

      --  For regular borrowers, go through the borrowed expression to collect
      --  constraints on borrowed components.

      Cur := Get_Borrowed_Expr (Brower);

      loop
         --  Assume that the constraints on Cur are preserved

         if Nkind (Cur) not in N_Type_Conversion
                             | N_Unchecked_Type_Conversion
                             | N_Qualified_Expression
                             | N_Slice
         then
            declare
               Ty    : constant Entity_Id := Retysp (Etype (Cur));
               W_Cur : constant W_Expr_Id := Transform_Expr
                 (Expr    => Cur,
                  Domain  => EW_Term,
                  Params  => Params);
               --  Expression for Cur rooted at Borrowed

               Cur_N : constant W_Expr_Id := Path_From_Name (Cur);
               --  Expression for Cur rooted at Borrowed_Id
            begin
               case Ekind (Ty) is

                  --  Bounds of borrowed components are preserved

                  when Array_Kind =>
                     if not Is_Static_Array_Type (Ty) then
                        Res := +New_And_Expr
                          (Domain => EW_Pred,
                           Left   => +New_Bounds_Equality
                             (Left_Arr  => W_Cur,
                              Right_Arr => Cur_N,
                              Dim       =>
                                Positive (Number_Dimensions (Ty))),
                           Right  => +Res);
                     end if;

                  --  Nullity of pointers is preserved. Note that in
                  --  general pointers will not be null in a path.
                  --  However, Path itself can be.
                  --  ??? We could also state that the address is
                  --  preserved.

                  when Access_Kind =>
                     Res := +New_And_Expr
                       (Domain => EW_Pred,
                        Left   =>
                           New_Comparison
                          (Symbol => Why_Eq,
                           Left   => New_Pointer_Is_Null_Access (Ty, W_Cur),
                           Right  => New_Pointer_Is_Null_Access (Ty, Cur_N),
                           Domain => EW_Pred),
                        Right  => +Res);

                  when others =>
                     pragma Assert (Is_Record_Type_In_Why (Ty));

                     --  Discriminants of borrowed components are preserved

                     if Has_Discriminants (Ty) then
                        declare
                           Discr : Entity_Id := First_Discriminant (Ty);
                        begin
                           loop
                              Res := +New_And_Expr
                                (Domain => EW_Pred,
                                 Left   => New_Comparison
                                   (Symbol  => Why_Eq,
                                    Left    => New_Ada_Record_Access
                                      (Ada_Node => Empty,
                                       Domain   => EW_Term,
                                       Name     => W_Cur,
                                       Field    => Discr,
                                       Ty       => Ty),
                                    Right   => New_Ada_Record_Access
                                      (Ada_Node => Empty,
                                       Domain   => EW_Term,
                                       Name     => Cur_N,
                                       Field    => Discr,
                                       Ty       => Ty),
                                    Domain  => EW_Pred),
                                 Right  => +Res);
                              Next_Discriminant (Discr);
                              exit when No (Discr);
                           end loop;
                        end;
                     end if;
               end case;
            end;
         end if;

         --  Go to the next prefix

         case Nkind (Cur) is
            when N_Expanded_Name | N_Identifier =>
               exit;

            when N_Type_Conversion
               | N_Unchecked_Type_Conversion
               | N_Qualified_Expression
            =>
               Cur := Expression (Cur);

            when N_Slice
               | N_Selected_Component
               | N_Indexed_Component
               | N_Explicit_Dereference
            =>
               Cur := Prefix (Cur);

            when others =>
               raise Program_Error;
         end case;
      end loop;
      return Res;
   end Compute_Assumption_For_Borrow;

   -----------------------
   -- Compute_Call_Args --
   -----------------------

   function Compute_Call_Args
     (Call    : Node_Id;
      Domain  : EW_Domain;
      Context : in out Ref_Context;
      Store   : W_Statement_Sequence_Unchecked_Id;
      Params  : Transformation_Params) return W_Expr_Array
   is
      Subp     : constant Entity_Id := Get_Called_Entity (Call);
      Binders  : constant Item_Array :=
        Compute_Subprogram_Parameters (Subp, Domain);
      Patterns : Item_Array := Binders;
      Aliasing : constant Boolean :=
        Nkind (Call) in N_Procedure_Call_Statement | N_Entry_Call_Statement
        and then Get_Aliasing_Status_For_Proof (Call) in
          Possible_Aliasing .. Unchecked;
      --  If aliasing can occur for this subprogram call, we should introduce
      --  intermediate variables for every parameters in order to avoid
      --  crashing inside Why3.

   begin
      Localize_Variable_Parts (Patterns);

      if Binders'Length = 0 then
         return (1 => +Void);
      end if;

      declare
         Why_Args : W_Expr_Array (1 .. Item_Array_Length (Binders));
         Arg_Cnt  : Positive := 1;
         Bind_Cnt : Positive := Binders'First;

         procedure Compute_Param (Formal : Entity_Id; Actual : Node_Id);
         --  Compute a Why expression for each parameter

         -------------------
         -- Compute_Param --
         -------------------

         procedure Compute_Param (Formal : Entity_Id; Actual : Node_Id) is
            Needs_Havoc   : constant Boolean :=
              Present (Formal)
              and then Ekind (Formal) = E_Out_Parameter
              and then
                (Obj_Has_Relaxed_Init (Formal)
                 or else Contains_Relaxed_Init_Parts (Etype (Formal)));
            --  In the case of out parameters that are initialized by proof,
            --  the memory used by the callee may not be initialized at
            --  subprogram start, even if the actual was initialized at
            --  subprogram call. We need to havoc out parameters before the
            --  call to simulate the absence of initial value.
            --  NB. This is because flow analysis does not check that we are
            --  not reading the parts with relaxed init of an out parameter in
            --  the precondition.

            Pattern       : Item_Type := Patterns (Bind_Cnt);
            Formal_T      : constant W_Type_Id :=
              Get_Why_Type_From_Item (Binders (Bind_Cnt));
            Is_Self       : constant Boolean :=
              Binders (Bind_Cnt).Kind = Concurrent_Self;
            Use_Var       : constant Boolean :=
            --  True if we should use the item for the actual.

              --  On external calls, we need to reconstruct the object if
              --  it is mutable as protected types can be in split form.

              (if Is_Self then not Is_External_Call (Call)

               --  Otherwise, we go through the expression if the actual is not
               --  an identifier, if aliasing can occur, or if the formal has
               --  asynchronous writers.

               else
                 (Present (Actual)
                  and then Is_Simple_Actual (Actual)
                  and then not Aliasing
                  and then not
                    Has_Async_Writers (Direct_Mapping_Id (Formal))));
            Fetch_Ty      : constant W_Type_Id :=
              (if not Is_Self
                 and then Has_Array_Type (Etype (Formal))
                 and then Get_Type_Kind (Formal_T) = EW_Split
               then EW_Abstract
                 (Etype (Formal),
                  Relaxed_Init => Is_Init_Wrapper_Type (Formal_T))
               else Formal_T);
            --  We use an abstract type for arrays so that bounds can be
            --  retrieved.

            Actual_Expr   : constant W_Expr_Id :=
            --  Expression for the actual

              (if Is_Self and then Is_External_Call (Call)
               then Transform_Expr
                 (Prefix (SPARK_Atree.Name (Call)),
                  Formal_T,
                  Domain,
                  Params)
               elsif Is_Self and Self_Is_Mutable
               then New_Deref (Right => Self_Name,
                               Typ   => Get_Typ (Self_Name))
               elsif Is_Self then +Self_Name

               --  Do not check initialization of out parameters. If the
               --  parameter is a scalar, no checks are introduced.
               --  ??? Should we check predicates if the type has a
               --  Default_Value?

               elsif Ekind (Formal) = E_Out_Parameter
               then Insert_Checked_Conversion
                 (Ada_Node => Actual,
                  Domain   =>
                    (if Is_Scalar_Type (Retysp (Etype (Formal)))
                       and then Domain = EW_Prog
                     then EW_Pterm else Domain),
                  Expr     => Transform_Expr
                    (Expr          => Actual,
                     Domain        => Domain,
                     Params        => Params),
                  To       => Fetch_Ty,
                  No_Init  => True)

               --  Otherwise, directly use the expected type for the conversion

               else Transform_Expr
                 (Expr          => Actual,
                  Domain        => Domain,
                  Params        => Params,
                  Expected_Type => Fetch_Ty));

            Actual_Tmp    : W_Expr_Id;
            --  Temporary identifier to store the actual expression

            Constr_Expr   : constant W_Expr_Id :=
              (if Pattern.Kind = DRecord
               and then Pattern.Constr.Present
               then New_Constrained_Attribute_Expr (Actual, Domain)
               else Why_Empty);
            --  Expression for the constrained attribute of split records

            Need_Store  : Boolean;

         begin
            --  Store the converted actual into a temporary constant to avoid
            --  computing it several times. It also ensures that checks are
            --  emitted even if the expression happens to not be used.
            --  If the formal is not mutable, we do not need a temporary for
            --  the expression as it will be used exactly once.
            --  We don't need a temporary for the self reference of protected
            --  objects is the call is internal.

            if Item_Is_Mutable (Pattern)
              and then (not Is_Self or else Is_External_Call (Call))
            then
               declare
                  Tmp_Id : constant W_Identifier_Id :=
                    New_Temp_Identifier
                      (Ada_Node  => Get_Ada_Node (+Actual_Expr),
                       Typ       => Get_Type (Actual_Expr),
                       Base_Name => "compl");
               begin
                  Actual_Tmp := +Tmp_Id;
                  Context.Append
                    (Ref_Type'(Mutable => False,
                               Name    => Tmp_Id,
                               Value   => Actual_Expr));
               end;
            else
               Actual_Tmp := Actual_Expr;
            end if;

            --  Handle the initialization flag. This flag is only present for
            --  out parameters. We initialize it to any boolean as the
            --  initialization is not preserved on entry for out parameters.
            --  We never try to reuse the reference for the initialization
            --  flag of the actual. Indeed, as per Ada's rules, the top-level
            --  init flag of an out parameter is always True on exit, so we
            --  can assign it directly.

            if Pattern.Init.Present then
               Context.Append
                 (Ref_Type'(Mutable => True,
                            Name    => Pattern.Init.Id,
                            Value   =>
                              New_Any_Expr
                                (Return_Type => EW_Bool_Type,
                                 Labels      => Symbol_Sets.Empty_Set)));
               Why_Args (Arg_Cnt) := +Pattern.Init.Id;
               Arg_Cnt := Arg_Cnt + 1;

               --  Remove the init flag on the pattern, as it was already
               --  handled.

               Pattern.Init := (Present => False);
            end if;

            --  For variable formals, we try to reuse parts of the actual for
            --  the variable parts of the formal if we can.

            if Use_Var and then Item_Is_Mutable (Pattern) then
               declare
                  Actual_Binder : constant Item_Type :=
                    (if Binders (Bind_Cnt).Kind = Concurrent_Self
                     then Item_Type'(Kind  => Concurrent_Self,
                                     Init  => <>,
                                     Local => True,
                                     Main  =>
                                       (B_Name  => Self_Name,
                                        Mutable => Self_Is_Mutable,
                                        others  => <>))
                     else Ada_Ent_To_Why.Element
                       (Symbol_Table, Entity (Actual)));
               begin
                  Get_Item_From_Var
                    (Pattern     => Pattern,
                     Var         => Actual_Binder,
                     Expr        => Actual_Tmp,
                     Context     => Context,
                     Args        => Why_Args (Arg_Cnt .. Why_Args'Length),
                     Constr_Expr => Constr_Expr,
                     Need_Store  => Need_Store);
               end;

            --  Otherwise, we create new references and initialize them from
            --  Actual_Tmp.

            else
               Get_Item_From_Expr
                 (Pattern     => Pattern,
                  Expr        => Actual_Tmp,
                  Context     => Context,
                  Args        => Why_Args (Arg_Cnt .. Why_Args'Length),
                  Constr_Expr => Constr_Expr,
                  Need_Store  => Need_Store);
            end if;

            --  If necessary, we havoc the references so that out parameters
            --  are never considered to be initialized.

            if Needs_Havoc then

               --  For records, we only need to havoc the reference for Fields.
               --  It is the first reference if there is one.

               if Pattern.Kind /= DRecord or else Pattern.Fields.Present then
                  Why_Args (Arg_Cnt) := +Sequence
                    (Left  => New_Havoc_Call (+Why_Args (Arg_Cnt)),
                     Right => +Why_Args (Arg_Cnt));
               end if;
            end if;

            --  If the item is mutable, compute in Store the statements to
            --  store the content of the temporaries back into the actual.

            if Item_Is_Mutable (Pattern) then
               Compute_Store
                 (Pattern        => Pattern,
                  Actual         =>
                    (if Is_Self and then Is_External_Call (Call)
                     then Prefix (SPARK_Atree.Name (Call))
                     else Actual),
                  Need_Store     => Need_Store,
                  No_Pred_Checks =>
                    Is_Self or else Eq_Base
                      (Type_Of_Node (Actual), Type_Of_Node (Formal)),
                  Pre_Expr       => Actual_Tmp,
                  Store          => Store,
                  Params         => Params);
            end if;

            Arg_Cnt := Arg_Cnt + Item_Array_Length ((1 => Pattern));

            Bind_Cnt := Bind_Cnt + 1;
         end Compute_Param;

         procedure Iterate_Call is new
           Iterate_Call_Parameters (Compute_Param);

      begin
         Statement_Sequence_Append_To_Statements (Store, +Void);

         --  In the case of protected subprograms, there is an invisible first
         --  parameter, the protected object itself. We call "Compute_Arg" with
         --  empty arguments to process this case.

         if Within_Protected_Type (Subp) then
            Compute_Param (Empty, Empty);
         end if;

         --  If the call is an operator, directly call Compute_Param on each of
         --  its operands.

         if Nkind (Call) in N_Op then
            declare
               Formal : Entity_Id := First_Formal (Subp);

            begin
               if Nkind (Call) in N_Binary_Op then
                  Compute_Param (Formal, Left_Opnd (Call));
                  Next_Formal (Formal);
               end if;

               Compute_Param (Formal, Right_Opnd (Call));
            end;

         --  Otherwise, iterate through the call parameters

         else
            Iterate_Call (Call);
         end if;

         --  Get values for global inputs of functions

         for B in Bind_Cnt .. Binders'Last loop
            Why_Args (Arg_Cnt .. Why_Args'Last) :=
              Get_Logic_Args (Subp, Params.Ref_Allowed);
         end loop;

         return Why_Args;
      end;
   end Compute_Call_Args;

   ---------------------------
   -- Compute_Default_Check --
   ---------------------------

   function Compute_Default_Check
     (Ada_Node         : Node_Id;
      Ty               : Entity_Id;
      Params           : Transformation_Params;
      Assume_Last_DIC  : Boolean := False;
      Include_Subtypes : Boolean := False;
      Decl_Node        : Node_Id := Empty) return W_Prog_Id
   is

      procedure Check_Or_Assume_DIC
        (Ada_Node   : Node_Id;
         Expr       : Node_Id;
         Params     : Transformation_Params;
         Checks     : in out W_Prog_Id;
         Assume_Exp : Boolean := False);
      --  Generate a program expression which asserts or assumes Expr and
      --  prepend it to Checks. If the Expr is asserted, also introduce checks
      --  for it. Only assume Expr if Checks is not empty.

      -------------------------
      -- Check_Or_Assume_DIC --
      -------------------------

      procedure Check_Or_Assume_DIC
        (Ada_Node   : Node_Id;
         Expr       : Node_Id;
         Params     : Transformation_Params;
         Checks     : in out W_Prog_Id;
         Assume_Exp : Boolean := False)
      is
      begin
         if Assume_Exp then
            if Checks /= +Void then
               Checks := Sequence
                 (New_Assume_Statement
                    (Ada_Node => Ada_Node,
                     Pred     => +Transform_Expr
                       (Expr    => Expr,
                        Domain  => EW_Pred,
                        Params  => Params)),
                  Checks);
            end if;
         else
            Checks := Sequence
              ((1 => New_Ignore
                (Ada_Node => Ada_Node,
                 Prog     => +Transform_Expr
                   (Expr    => Expr,
                    Domain  => EW_Prog,
                    Params  => Params)),
                2 => New_Located_Assert
                  (Ada_Node => Ada_Node,
                   Kind     => EW_Check,
                   Reason   => VC_Default_Initial_Condition,
                   Pred     => +Transform_Expr
                     (Expr    => Expr,
                      Domain  => EW_Pred,
                      Params  => Params)),
                3 => Checks));
         end if;
      end Check_Or_Assume_DIC;

      --  If Ty's fullview is in SPARK, go to its underlying type to check its
      --  kind.

      Ty_Ext : constant Entity_Id := Retysp (Ty);
      Checks : W_Prog_Id := +Void;

   --  Start of processing for Compute_Default_Check

   begin

      if Has_Predicates (Ty)
        and then Default_Initialization (Ty) /= No_Default_Initialization
      then
         declare
            W_Typ   : constant W_Type_Id := EW_Abstract
              (Ty_Ext, Relaxed_Init => Has_Relaxed_Init (Ty_Ext));
            --  Even if we are checking the default initialization of an object
            --  with relaxed initialization, we only assume for checking the
            --  predicate that the value may have relaxed initialization if
            --  the type itself is marked with relaxed init. Indeed, otherwise,
            --  the predicate assumes complete initialization.

            Tmp_Exp : constant W_Identifier_Id :=
              New_Temp_Identifier (Ty_Ext, W_Typ);
            --  Temporary variable for tmp_exp

            --  Create a value of type Ty_Ext that respects the default
            --  initialization value for Ty_Ext, except its default initial
            --  condition when specified. Since we use an any-expr, the
            --  predicate needs to apply to the special "result" term.

            Default_Init_Pred : constant W_Pred_Id :=
              Compute_Default_Init
                (Expr             => +New_Result_Ident (W_Typ),
                 Ty               => Ty_Ext,
                 Params           => Params,
                 Include_Subtypes => Include_Subtypes,
                 Skip_Last_Cond   => (if Has_DIC (Ty_Ext)
                                      and then Needs_DIC_Check_At_Decl (Ty_Ext)
                                      then True_Term
                                      else False_Term));
            --  If the DIC is checked at use, we can safely assume it here. If
            --  it is checked on declaration, then it is checked assuming that
            --  the predicate of Ty_Ext holds, so we should not assume it here.

            Default_Init_Prog : constant W_Prog_Id :=
              New_Any_Expr (Ada_Node    => Ty_Ext,
                            Labels      => Symbol_Sets.Empty_Set,
                            Post        => Default_Init_Pred,
                            Return_Type => W_Typ);

            --  Generate the predicate check, specifying that it applies to the
            --  default value of a type, so that a special VC kind is used for
            --  better messages.

            Pred_Check : constant W_Prog_Id :=
              New_Predicate_Check
                (Ada_Node         => Ada_Node,
                 Ty               => Ty,
                 W_Expr           => +Tmp_Exp,
                 On_Default_Value => True);

         begin
            Checks := Sequence
              (Checks,
               New_Ignore
                 (Prog => +New_Typed_Binding
                      (Domain  => EW_Prog,
                       Name    => Tmp_Exp,
                       Def     => +Default_Init_Prog,
                       Context => +Pred_Check)));
         end;
      end if;

      if Is_Scalar_Type (Ty) then
         if Has_Default_Aspect (Ty_Ext) then
            declare
               Default_Expr : constant W_Expr_Id :=
                 Transform_Expr
                   (Expr          => Default_Aspect_Value (Ty_Ext),
                    Expected_Type => Base_Why_Type (Ty_Ext),
                    Domain        => EW_Prog,
                    Params        => Params);

               --  Do not check predicate of default value, it will be done
               --  later.

               Range_Check  : constant W_Expr_Id :=
                 Insert_Scalar_Conversion
                   (Domain     => EW_Prog,
                    Ada_Node   => Default_Aspect_Value (Ty_Ext),
                    Expr       => Default_Expr,
                    To         => Type_Of_Node (Ty_Ext),
                    Range_Type => Ty_Ext,
                    Check_Kind => RCK_Range,
                    Skip_Pred  => True);
            begin
               Checks := Sequence
                 (Checks,
                  +Range_Check);
            end;
         end if;

      elsif Is_Array_Type (Ty)
        and then Ekind (Ty) /= E_String_Literal_Subtype
      then
         pragma Assert (Is_Constrained (Ty_Ext) or else Include_Subtypes);

         --  Generates:
         --  length (Index_Type1) > 0 /\ .. ->
         --    Default_Component_Value         <if any>
         --    default_checks (Component_Type) <otherwise>

         declare
            Range_Expr : W_Prog_Id := True_Prog;
            Num_Dim    : constant Positive :=
              Positive (Number_Dimensions (Ty_Ext));
            T_Comp     : W_Expr_Id;

         begin
            --  Generate the condition length (Index_Type1) > 0 /\ ..

            if Is_Constrained (Ty_Ext) then
               for Dim in 1 .. Num_Dim loop
                  Range_Expr := +New_And_Expr
                    (Left   => +Range_Expr,
                     Right  => New_Comparison
                       (Symbol => Int_Infix_Gt,
                        Left   => Build_Length_Expr
                          (Domain => EW_Prog,
                           Ty     => Ty_Ext,
                           Dim    => Dim),
                        Right  => New_Integer_Constant (Empty, Uint_0),
                        Domain => EW_Prog),
                     Domain => EW_Prog);
               end loop;
            end if;

            --  Generate the check for the default value of Component_Type
            --    Default_Component_Value         <if any>
            --    default_checks (Component_Type) <otherwise>

            --  If Ty_Ext has a Default_Component_Value aspect, use it

            if Has_Default_Aspect (Ty_Ext) then
               T_Comp := Transform_Expr
                 (Expr          => Default_Aspect_Component_Value (Ty_Ext),
                  Expected_Type => Type_Of_Node (Component_Type (Ty_Ext)),
                  Domain        => EW_Prog,
                  Params        => Params);

            --  Otherwise, use its Component_Type default value

            else
               T_Comp := +Compute_Default_Check
                 (Ada_Node => Ada_Node,
                  Ty       => Component_Type (Ty_Ext),
                  Params   => Params);
            end if;

            if T_Comp /= +Void then
               T_Comp := New_Conditional
                 (Ada_Node    => Ty,
                  Domain      => EW_Prog,
                  Condition   => +Range_Expr,
                  Then_Part   => +New_Ignore
                    (Component_Type (Ty_Ext), +T_Comp));

               Checks := Sequence (Checks, +T_Comp);
            end if;
         end;

      elsif Is_Record_Type_In_Why (Ty) then

         --  Generates:
         --  let tmp1 = Discr1.default in <if Ty_Ext is unconstrained>
         --  let tmp1 = Discr1 in         <if Ty_Ext is constrained>
         --  let tmp_exp = any <type> ensures { result.discr1 = tmp1 .. } in
         --  (check_for_f1 expr ->
         --          Field1.default                  <if Field1 has a default>
         --          default_check (Etype (Field1))) <otherwise>
         --  /\ ..

         Ada_Ent_To_Why.Push_Scope (Symbol_Table);

         declare
            Tmp_Exp : constant W_Identifier_Id :=
              New_Temp_Identifier (Ty_Ext, EW_Abstract (Ty_Ext));
            --  Temporary variable for tmp_exp

            Post    : W_Pred_Id := True_Pred;
            --  Post used for the assignment of tmp_exp

            Discrs  : constant Natural := Count_Discriminants (Ty_Ext);
            Tmps    : W_Identifier_Array (1 .. Discrs);
            Binds   : W_Expr_Array (1 .. Discrs);
            --  Arrays to store the bindings for discriminants

            Discr   : Node_Id := (if Discrs > 0
                                  then First_Discriminant (Ty_Ext)
                                  else Empty);
            Elmt    : Elmt_Id :=
              (if Discrs > 0
               and then Is_Constrained (Ty_Ext) then
                    First_Elmt (Discriminant_Constraint (Ty_Ext))
               else No_Elmt);
            T_Comp  : W_Expr_Id;
            I       : Positive := 1;
         begin

            --  Go through discriminants to create the bindings for
            --  let tmp1 = Discr1.default in <if Ty_Ext is unconstrained>
            --  let tmp1 = Discr1 in         <if Ty_Ext is constrained>
            --  Also fills Post with { result.discr1 = tmp1 /\ .. }

            while Present (Discr) loop
               Tmps (I) := New_Temp_Identifier
                 (Discr, Type_Of_Node (Etype (Discr)));

               Insert_Entity (Discr, Tmps (I));

               if Is_Constrained (Ty_Ext) then

                  --  Store constrained value of discriminants

                  Binds (I) :=
                    Transform_Expr
                      (Domain        => EW_Prog,
                       Params        => Params,
                       Expr          => Node (Elmt),
                       Expected_Type => Type_Of_Node (Etype (Discr)));
                  Next_Elmt (Elmt);
               elsif not Include_Subtypes then
                  pragma Assert (Has_Defaulted_Discriminants (Ty_Ext));

                  --  Store default value of discriminants for unconstrained
                  --  record types with default discriminants.

                  Binds (I) :=
                    Transform_Expr
                      (Expr          => Discriminant_Default_Value (Discr),
                       Expected_Type => Type_Of_Node (Etype (Discr)),
                       Domain        => EW_Prog,
                       Params        => Params);
               else
                  Binds (I) :=
                    +New_Any_Statement
                    (Post        => Compute_Dynamic_Invariant
                       (Expr        => +New_Result_Ident
                            (Type_Of_Node (Etype (Discr))),
                        Ty          => Etype (Discr),
                        Initialized => True_Term,
                        Params      => Body_Params),
                     Return_Type => Type_Of_Node (Etype (Discr)));
               end if;

               --  Add new Equality tmp = result.discr to Post

               Post := +New_And_Then_Expr
                 (Left   => +Post,
                  Right  => New_Comparison
                    (Symbol => Why_Eq,
                     Left   => +Tmps (I),
                     Right  => Insert_Simple_Conversion
                       (Domain => EW_Term,
                        Expr   => New_Ada_Record_Access
                          (Ada_Node => Empty,
                           Domain   => EW_Term,
                           Name     =>
                             +New_Result_Ident (EW_Abstract (Ty_Ext)),
                           Field    => Discr,
                           Ty       => Ty_Ext),
                        To     => Type_Of_Node (Etype (Discr))),
                     Domain => EW_Pred),
                  Domain => EW_Pred);

               Next_Discriminant (Discr);
               I := I + 1;
            end loop;

            --  Go through other fields to create the expression
            --  (check_for_f1 expr ->
            --        Field1.default                  <if Field1 has a default>
            --        default_check (Etype (Field1))) <otherwise>
            --  /\ ..
            --  Components of protected types are checked when generating VCs
            --  for the protected type.
            --  If Decl_Node is Empty, do not generate checks for components
            --  of private types.
            --  If Decl_Node is a private extension, do not generate checks for
            --  inherited components.
            --  Do not generate checks for hidden components, they will be
            --  checked at the place where they are hidden.

            if not Is_Concurrent_Type (Ty_Ext)
              and then (Is_Record_Type (Ty) or else Present (Decl_Node))
            then
               declare
                  Checks_Seq : W_Statement_Sequence_Id := Void_Sequence;
               begin
                  for Field of Get_Component_Set (Ty_Ext) loop
                     if Component_Is_Visible_In_Type (Ty, Field)
                       and then
                         (Nkind (Decl_Node) /= N_Private_Extension_Declaration
                          or else Original_Declaration (Field) = Ty_Ext)
                     then
                        if Present (Expression (Enclosing_Declaration (Field)))
                        then

                           --  If Field has a default expression, use it

                           T_Comp := Transform_Expr
                             (Expr          =>
                                Expression (Enclosing_Declaration (Field)),
                              Expected_Type => Type_Of_Node (Etype (Field)),
                              Domain        => EW_Prog,
                              Params        => Params);
                        else

                           --  Otherwise, use its Field's Etype default value

                           T_Comp :=
                             +Compute_Default_Check
                             (Field, Etype (Field), Params);
                        end if;

                        if T_Comp /= +Void then

                           --  Check values of record fields only if they are
                           --  in the proper variant part.

                           T_Comp  := New_Conditional
                             (Domain    => EW_Prog,
                              Condition => New_Ada_Record_Check_For_Field
                                (Empty, EW_Prog, +Tmp_Exp, Field, Ty_Ext),
                              Then_Part =>
                                +New_Ignore
                                (Ada_Node => Etype (Field),
                                 Prog     => +T_Comp));
                           Sequence_Append (Checks_Seq, +T_Comp);

                        end if;
                     end if;
                  end loop;

                  Checks := Sequence
                    (Left  => Checks,
                     Right => +Checks_Seq);
               end;
            end if;

            --  Assume the default initial condition here as it may refer to
            --  discriminant values.

            if Has_Discriminants (Ty)
              and then Has_DIC (Ty)
              and then Needs_DIC_Check_At_Use (Ty)
            then
               declare
                  Default_Init_Subp  : constant Entity_Id :=
                    Get_Initial_DIC_Procedure (Ty);
                  Default_Init_Expr  : constant Node_Id :=
                    Get_Expr_From_Check_Only_Proc (Default_Init_Subp);
                  Default_Init_Param : constant Entity_Id :=
                    First_Formal (Default_Init_Subp);

               begin
                  if Present (Default_Init_Expr) then

                     --  Add the binder for the reference to the type to the
                     --  Symbol_Table.

                     Ada_Ent_To_Why.Push_Scope (Symbol_Table);

                     Insert_Entity
                       (Default_Init_Param,
                        Tmp_Exp,
                        Mutable => False);

                     Check_Or_Assume_DIC
                       (Ada_Node   => Ada_Node,
                        Expr       => Default_Init_Expr,
                        Params     => Params,
                        Checks     => Checks,
                        Assume_Exp => Assume_Last_DIC);

                     Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
                  end if;
               end;
            end if;

            --  Create bindings for Tmp_Exp
            --  let expr = any <type> ensures { expr.discr1 = tmp1 .. } in

            if Checks /= +Void then
               Checks := +New_Typed_Binding
                 (Domain   => EW_Prog,
                  Name     => Tmp_Exp,
                  Def      =>
                    New_Any_Expr (Ada_Node    => Ty_Ext,
                                  Labels      => Symbol_Sets.Empty_Set,
                                  Post        => Post,
                                  Return_Type => EW_Abstract (Ty_Ext)),
                  Context  => +Checks);

            end if;

            --  Generate the bindings if we have some fields to check or if we
            --  need to check the bindings themselves.

            if Checks /= +Void or else not Is_Constrained (Ty) then
               for I in 1 .. Discrs loop
                  Checks := +New_Typed_Binding
                    (Domain   => EW_Prog,
                     Name     => Tmps (I),
                     Def      => Binds (I),
                     Context  => +Checks);
               end loop;
            end if;
         end;
         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      end if;

      --  If Ty has a DIC and this DIC should be checked at use (it does not
      --  reference the current type instance), check that there is no runtime
      --  error in the DIC and that the DIC holds.
      --  If Ty has discriminants, this has been done earlier.

      if Has_DIC (Ty)
        and then Needs_DIC_Check_At_Use (Ty)
        and then not Has_Discriminants (Ty)
      then
         declare
            Default_Init_Subp  : constant Entity_Id :=
              Get_Initial_DIC_Procedure (Ty);
            Default_Init_Expr  : constant Node_Id :=
              Get_Expr_From_Check_Only_Proc (Default_Init_Subp);

         begin
            if Present (Default_Init_Expr) then

               --  No need to add a binder, the DIC should have no reference
               --  to the type instance.

               Check_Or_Assume_DIC
                 (Ada_Node   => Ada_Node,
                  Expr       => Default_Init_Expr,
                  Params     => Params,
                  Checks     => Checks,
                  Assume_Exp => Assume_Last_DIC);
            end if;
         end;
      end if;

      return Checks;
   end Compute_Default_Check;

   --------------------------
   -- Compute_Default_Init --
   --------------------------

   function Compute_Default_Init
     (Expr             : W_Expr_Id;
      Ty               : Entity_Id;
      Params           : Transformation_Params := Body_Params;
      Skip_Last_Cond   : W_Term_Id := False_Term;
      Use_Pred         : Boolean := True;
      Include_Subtypes : Boolean := False) return W_Pred_Id
   is

      Ty_Ext : constant Entity_Id := Retysp (Ty);

      function Default_Init_For_Comp
        (C_Expr : W_Term_Id;
         C_Ty   : Entity_Id)
         return W_Pred_Id
      with Pre => Is_Type (C_Ty);
      --  @param C_Expr expression for an array component
      --  @param C_Ty array component type
      --  @return predicate for individual array components
      --    <C_Expr> = <Default_Component_Value>  <if Ty has a default aspect>
      --    default_init (<C_Expr>), C_Ty)        <otherwise>

      function Default_Init_For_Field
        (F_Expr : W_Term_Id;
         F_Ty   : Entity_Id;
         E      : Entity_Id)
         return W_Pred_Id
      with Pre => Is_Type (F_Ty)
                    and then
                  (Ekind (E) = E_Component
                   or else Is_Part_Of_Protected_Object (E));
      --  @param F_Expr expression for the component
      --  @param F_Ty component type
      --  @param E node for a record component
      --  @return predicate for individual record components
      --   F_Expr = E.def               <if Field1 has a default>
      --   default_init (F_Expr, F_Ty)) <otherwise>

      function Default_Init_For_Discr
        (D_Expr : W_Term_Id;
         D_Ty   : Entity_Id;
         E      : Entity_Id)
         return W_Pred_Id
      with Pre => Is_Type (D_Ty) and then Ekind (E) = E_Discriminant;
      --  @param D_Expr expression for the discrimiant
      --  @param D_Ty discriminant type
      --  @param E node for a discriminant
      --  @return predicate for individual discrimiant
      --  D_Expr = E.default             <if Ty_Ext is unconstrained>
      --  D_Expr = stored_constraint (E) <otherwise>

      ---------------------------
      -- Default_Init_For_Comp --
      ---------------------------

      function Default_Init_For_Comp
        (C_Expr : W_Term_Id;
         C_Ty   : Entity_Id) return W_Pred_Id
      is
         P : W_Pred_Id;
      begin
         if Has_Default_Aspect (Ty_Ext) then
            P := +New_Comparison
              (Symbol => Why_Eq,
               Left   => Insert_Simple_Conversion
                 (Domain => EW_Term,
                  Expr   => +C_Expr,
                  To     => Type_Of_Node (C_Ty)),
               Right  => Transform_Expr
                 (Expr          => Default_Aspect_Component_Value (Ty_Ext),
                  Expected_Type => Type_Of_Node (C_Ty),
                  Domain        => EW_Term,
                  Params        => Params),
               Domain => EW_Pred);

         else
            P := Compute_Default_Init
                    (Expr     => +C_Expr,
                     Ty       => C_Ty,
                     Params   => Params,
                     Use_Pred => Use_Pred);
         end if;

         --  If C_Ty has a wrapper for initialization, set the init flag

         if Is_Init_Wrapper_Type (Get_Type (+C_Expr))
           and then Has_Default_Aspect (Ty_Ext)
         then
            P := +New_And_Expr
              (Left   => +P,
               Right  => +Compute_Is_Initialized
                 (C_Ty, +C_Expr, Params.Ref_Allowed, Domain => EW_Pred),
               Domain => EW_Pred);
         end if;

         return P;
      end Default_Init_For_Comp;

      ----------------------------
      -- Default_Init_For_Discr --
      ----------------------------

      function Default_Init_For_Discr
        (D_Expr : W_Term_Id;
         D_Ty   : Entity_Id;
         E      : Entity_Id)
         return W_Pred_Id
      is
      begin
         --  If the type is constrained, get the value of discriminants from
         --  the stored constraints.

         if Count_Discriminants (Ty_Ext) > 0
           and then Is_Constrained (Ty_Ext)
         then
            return +New_Comparison
              (Symbol => Why_Eq,
               Left   => +Insert_Simple_Conversion
                 (Domain => EW_Term,
                  Expr   => +D_Expr,
                  To     => Type_Of_Node (D_Ty)),
               Right  => Transform_Expr
                 (Domain        => EW_Term,
                  Params        => Params,
                  Expr          => Get_Constraint_For_Discr (Ty_Ext, E),
                  Expected_Type => Type_Of_Node (D_Ty)),
               Domain => EW_Pred);

         --  Default initialized objects of an unconstrained record type have
         --  the discriminant's defaults.

         elsif not Include_Subtypes then
            pragma Assert (Has_Defaulted_Discriminants (Ty_Ext));

            return +New_Comparison
              (Symbol => Why_Eq,
               Left   => +Insert_Simple_Conversion
                 (Domain => EW_Term,
                  Expr   => +D_Expr,
                  To     => Type_Of_Node (D_Ty)),
               Right  => Transform_Expr
                 (Expr          =>
                      Discriminant_Default_Value (E),
                  Expected_Type =>
                    Type_Of_Node (D_Ty),
                  Domain        => EW_Term,
                  Params        => Params),
               Domain => EW_Pred);

         --  Discriminants must be initialized

         else
            return Compute_Dynamic_Invariant
              (D_Expr, D_Ty, Initialized => True_Term,
               Params => Params, Use_Pred => Use_Pred);
         end if;
      end Default_Init_For_Discr;

      ----------------------------
      -- Default_Init_For_Field --
      ----------------------------

      function Default_Init_For_Field
        (F_Expr : W_Term_Id;
         F_Ty   : Entity_Id;
         E      : Entity_Id)
         return W_Pred_Id
      is
         P : W_Pred_Id;
      begin
         --  if Field has a default expression, use it.
         --   <Expr>.rec__field1 = Field1.default

         --  Access type fields cannot have default initialization. Such fields
         --  should not exist in the Ada declaration.

         if Present (Expression (Enclosing_Declaration (E))) then
            P := +New_Comparison
              (Symbol => Why_Eq,
               Left   => Insert_Simple_Conversion
                 (Domain => EW_Term,
                  Expr   => +F_Expr,
                  To     => Type_Of_Node (F_Ty)),
               Right  => New_Tag_Update
                 (Domain => EW_Term,
                  Name   => Transform_Expr
                    (Expr          => Expression (Enclosing_Declaration (E)),
                     Expected_Type => Type_Of_Node (F_Ty),
                     Domain        => EW_Term,
                     Params        => Params),
                  Ty     => F_Ty),
               Domain => EW_Pred);

            --  otherwise, use its Field's Etype default value.
            --   default_init (<Expr>.rec__field1, Etype (Field1)))

         else
            P := +Compute_Default_Init
              (+F_Expr,
               F_Ty,
               Params => Params,
               Use_Pred => Use_Pred);
         end if;

         --  If F_Ty has a wrapper for initialization, set the init flag

         if Is_Init_Wrapper_Type (Get_Type (+F_Expr))
           and then Present (Expression (Enclosing_Declaration (E)))
         then
            P := +New_And_Expr
              (Left   => +P,
               Right  => +Compute_Is_Initialized
                    (F_Ty, +F_Expr, Params.Ref_Allowed, Domain => EW_Pred),
               Domain => EW_Pred);
         end if;

         return P;
      end Default_Init_For_Field;

      function Default_Init_For_Array is new Build_Predicate_For_Array
        (Default_Init_For_Comp);

      function Default_Init_For_Record is new Build_Predicate_For_Record
        (Default_Init_For_Discr, Default_Init_For_Field);

      Tmp        : constant W_Expr_Id := New_Temp_For_Expr (Expr);
      Assumption : W_Pred_Id := True_Pred;
      Variables  : Flow_Id_Sets.Set;

   --  Start of processing for Compute_Default_Init

   begin
      --  If Use_Precomputed_Func is true, then we already have generated a
      --  predicate for the default initial value of elements of type Ty_Ext,
      --  except if the type is an itype or if it is standard boolen.

      if Use_Pred
        and then not Include_Subtypes
        and then not Is_Itype (Ty_Ext)
        and then not Is_Standard_Boolean_Type (Ty_Ext)
        and then not Is_Init_Wrapper_Type (Get_Type (Expr))
      then
         Variables_In_Default_Init (Ty_Ext, Variables);

         declare
            Vars  : constant W_Expr_Array :=
              Get_Args_From_Variables (Variables, Params.Ref_Allowed);

            Num_B : constant Positive := 2 + Vars'Length;
            Args  : W_Expr_Array (1 .. Num_B);
         begin

            Args (1) := Insert_Simple_Conversion
              (Domain         => EW_Term,
               Expr           => Expr,
               To             => Type_Of_Node (Ty_Ext),
               Force_No_Slide => True);
            Args (2) := +Skip_Last_Cond;
            Args (3 .. Num_B) := Vars;

            return New_Call (Name => E_Symb (Ty_Ext, WNE_Default_Init),
                             Args => Args,
                             Typ  => EW_Bool_Type);
         end;
      elsif Is_Scalar_Type (Ty_Ext) then
         if Has_Default_Aspect (Ty_Ext) then
            declare
               Default_Expr : constant W_Expr_Id :=
                 Transform_Expr
                   (Expr          => Default_Aspect_Value (Ty_Ext),
                    Expected_Type => Base_Why_Type (Ty_Ext),
                    Domain        => EW_Term,
                    Params        => Params);
            begin
               Assumption := +New_Comparison
                 (Symbol => Why_Eq,
                  Left   => Insert_Simple_Conversion
                    (Ada_Node => Empty,
                     Domain   => EW_Pred,
                     Expr     => Tmp,
                     To       => Base_Why_Type (Ty_Ext)),
                  Right  => Default_Expr,
                  Domain => EW_Pred);
            end;
         end if;
      elsif Is_Array_Type (Ty_Ext)
        and then Ekind (Ty_Ext) /= E_String_Literal_Subtype
      then

         --  Generates:
         --  forall i1 : int ..
         --   in_range (i1) /\ .. ->
         --    get (<Expr>, i1, ...) = <Default_Component_Value>    <if any>
         --    default_init (get (<Expr>, i1, ...), Component_Type) <otherwise>

         Assumption := Default_Init_For_Array (+Expr, Ty_Ext);

         --  If Ty_Ext is constrained, also assume the array bounds

         if Is_Constrained (Ty_Ext)
           and then not Is_Static_Array_Type (Ty_Ext)
         then
            Assumption :=
              +New_And_Expr
                (Left   => +New_Bounds_Equality
                   (Expr, Ty_Ext, Params => Params),
                 Right  => +Assumption,
                 Domain => EW_Pred);
         end if;

      elsif Is_Access_Type (Ty_Ext) then

         Assumption := Pred_Of_Boolean_Term
           (+New_Pointer_Is_Null_Access (Ty_Ext, Expr));

      elsif Is_Record_Type_In_Why (Ty_Ext) then

         --  Generates:
         --  let tmp1 = <Expr>.rec__disc1 in
         --   <if Ty_Ext as default discrs>
         --  <Expr>.rec__disc1 = Discr1.default  <if Ty_Ext is unconstrained>
         --  <Expr>.rec__disc1 = Discr1 /\ ..    <if Ty_Ext is constrained>
         --  (check_for_field1 expr ->
         --      <Expr>.rec__field1 = Field1.def      <if Field1 has a default>
         --      default_init (<Expr>.rec__field1, Etype (Field1))) <otherwise>
         --  /\ ..

         --  if Ty_Ext is tagged, generate
         --     <Expr>.attr__tag = <Ty_Ext>.__tag

         if Is_Tagged_Type (Ty_Ext) then
            Assumption :=
              +New_And_Expr
              (Left   => New_Call
                 (Domain => EW_Pred,
                  Typ    => EW_Bool_Type,
                  Name   => Why_Eq,
                  Args =>
                    (1 => New_Tag_Access
                         (Ada_Node => Ty,
                          Domain   => EW_Term,
                          Name     => Tmp,
                          Ty       => Ty_Ext),
                     2 => +E_Symb (Ty_Ext, WNE_Tag))),
               Right  => +Assumption,
               Domain => EW_Pred);
         end if;

         Assumption :=
           +New_And_Expr
           (Left   => +Assumption,
            Right  => +Default_Init_For_Record (+Expr, Ty_Ext),
            Domain => EW_Pred);
      end if;

      --  If Skip_Last_Cond is False, assume the default initial condition for
      --  Ty, when specified as a boolean expression.

      if Has_DIC (Ty) then
         declare
            Init_Subp : constant Entity_Id := Get_Initial_DIC_Procedure (Ty);
         begin
            if Present (Init_Subp) then
               declare
                  Init_Expr : constant Node_Id :=
                    Get_Expr_From_Check_Only_Proc (Init_Subp);
                  Init_Param : constant Entity_Id := First_Formal (Init_Subp);
                  Init_Id    : constant W_Identifier_Id :=
                    New_Temp_Identifier (Init_Param, Get_Type (Tmp));
                  T          : W_Pred_Id;

               begin
                  if Present (Init_Expr) then
                     Ada_Ent_To_Why.Push_Scope (Symbol_Table);

                     --  Register the temporary identifier Init_Id for
                     --  parameter Init_Param in the symbol table. This ensures
                     --  both that a distinct name is used each time
                     --  (preventing name capture), and that the type of Tmp is
                     --  used as the type used to represent Init_Param
                     --  (avoiding type conversion).

                     Insert_Entity (Init_Param, Init_Id);

                     --  Transform the default init expression into Why3

                     T := +Transform_Expr (Expr   => Init_Expr,
                                           Domain => EW_Pred,
                                           Params => Params);

                     --  Relate the name Init_Id used in the default init
                     --  expression to the value Tmp for which the predicate is
                     --  checked.

                     T := New_Binding (Name    => Init_Id,
                                       Def     => Tmp,
                                       Context => +T,
                                       Typ     => Get_Type (+T));

                     --  Only take default init condition into account if
                     --  Skip_Last_Cond is False.

                     T := New_Conditional (Condition => +Skip_Last_Cond,
                                           Then_Part => +True_Pred,
                                           Else_Part => +T,
                                           Typ       => EW_Bool_Type);

                     Assumption := +New_And_Then_Expr (Left   => +Assumption,
                                                       Right  => +T,
                                                       Domain => EW_Pred);

                     Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
                  end if;
               end;
            end if;
         end;
      end if;

      if Assumption = +True_Pred then
         return True_Pred;
      else
         return +Binding_For_Temp
           (Domain => EW_Pred, Tmp => Tmp, Context => +Assumption);
      end if;
   end Compute_Default_Init;

   -------------------------------
   -- Compute_Dynamic_Invariant --
   -------------------------------

   function Compute_Dynamic_Invariant
     (Expr             : W_Term_Id;
      Ty               : Entity_Id;
      Params           : Transformation_Params;
      Initialized      : W_Term_Id := True_Term;
      Only_Var         : W_Term_Id := True_Term;
      Top_Predicate    : W_Term_Id := True_Term;
      Include_Type_Inv : W_Term_Id := True_Term;
      Use_Pred         : Boolean := True) return W_Pred_Id
   is
      T               : W_Pred_Id;
      New_Incompl_Acc : Ada_To_Why_Ident.Map;
   begin
      Compute_Dynamic_Invariant
        (Expr             => Expr,
         Ty               => Ty,
         Params           => Params,
         Initialized      => Initialized,
         Only_Var         => Only_Var,
         Top_Predicate    => Top_Predicate,
         Include_Type_Inv => Include_Type_Inv,
         Use_Pred         => Use_Pred,
         New_Preds_Module => Why_Empty,
         T                => T,
         Loc_Incompl_Acc  => Ada_To_Why_Ident.Empty_Map,
         New_Incompl_Acc  => New_Incompl_Acc,
         Expand_Incompl   => True);

      pragma Assert (New_Incompl_Acc.Is_Empty);
      return T;
   end Compute_Dynamic_Invariant;

   procedure Compute_Dynamic_Invariant
     (Expr             : W_Term_Id;
      Ty               : Entity_Id;
      Params           : Transformation_Params;
      Initialized      : W_Term_Id;
      Only_Var         : W_Term_Id;
      Top_Predicate    : W_Term_Id;
      Include_Type_Inv : W_Term_Id;
      Use_Pred         : Boolean;
      New_Preds_Module : W_Module_Id;
      T                : out W_Pred_Id;
      Loc_Incompl_Acc  : Ada_To_Why_Ident.Map;
      New_Incompl_Acc  : in out Ada_To_Why_Ident.Map;
      Expand_Incompl   : Boolean)
   is

      function Invariant_For_Access
        (Expr : W_Expr_Id; Ty : Entity_Id) return W_Pred_Id;
      --  Generates:
      --  (not <Expr>.is_null -> Dynamic_Invariant <Expr>.value)

      function Invariant_For_Comp
        (C_Expr : W_Term_Id; C_Ty : Entity_Id; E : Entity_Id)
         return W_Pred_Id;
      --  @param C_Expr expression for a component
      --  @param C_Ty component type
      --  @param E not referenced
      --  @return predicate for individual components
      --          Dynamic_Invariant <C_Expr>
      --              /\ C_Expr.rec__constrained = <Is_Constrained (C_Ty)>

      function Invariant_For_Comp
        (C_Expr : W_Term_Id; C_Ty : Entity_Id)
         return W_Pred_Id
        is (Invariant_For_Comp (C_Expr, C_Ty, Empty));

      --------------------------
      -- Invariant_For_Access --
      --------------------------

      function Invariant_For_Access
        (Expr : W_Expr_Id; Ty : Entity_Id) return W_Pred_Id
      is
         Value_Dyn_Inv : W_Pred_Id;
      begin

         --  ??? we can assume the value of constrained attribute if any

         Compute_Dynamic_Invariant
           (Expr             => +New_Pointer_Value_Access
              (Ada_Node => Empty,
               E        => Ty,
               Name     => +Expr,
               Domain   => EW_Term),
            Ty               => Directly_Designated_Type (Ty),
            Only_Var         => False_Term,
            Top_Predicate    => True_Term,
            Include_Type_Inv => Include_Type_Inv,
            Initialized      => True_Term,
            Params           => Params,
            Use_Pred         => Use_Pred,
            New_Preds_Module => New_Preds_Module,
            T                => Value_Dyn_Inv,
            Loc_Incompl_Acc  => Loc_Incompl_Acc,
            New_Incompl_Acc  => New_Incompl_Acc,
            Expand_Incompl   => False);
         --  Do not expand incomplete types inside access types to avoid
         --  hitting circularity.

         if Value_Dyn_Inv /= True_Pred then
            return New_Conditional
              (Condition =>
                 New_Not (Domain => EW_Pred,
                          Right  => New_Pointer_Is_Null_Access
                            (E    => Ty,
                             Name => +Expr)),
               Then_Part => +Value_Dyn_Inv);
         else
            return True_Pred;
         end if;
      end Invariant_For_Access;

      ------------------------
      -- Invariant_For_Comp --
      ------------------------

      function Invariant_For_Comp
        (C_Expr : W_Term_Id; C_Ty : Entity_Id; E : Entity_Id)
         return W_Pred_Id
      is
         T_Comp : W_Pred_Id;
      begin

         --  Recursively call Compute_Dynamic_Invariant on the composite type's
         --  components. Additional parameters are unchanged expect for
         --  Only_Var set to false (as a constant subcomponent of a variable
         --  toplevel object needs to be considered as variable too) and
         --  Top_Predicate set to true (as the decision to include or not
         --  the top predicate does not apply to subcomponents).
         --  Also discriminants and components of protected types are always
         --  initialized.

         Compute_Dynamic_Invariant
           (Expr             => C_Expr,
            Ty               => C_Ty,
            Initialized      =>
              (if (Present (E) and then Ekind (E) = E_Discriminant)
               or else Is_Protected_Type (Retysp (Ty))
               then True_Term
               else Initialized),
            Only_Var         => False_Term,
            Top_Predicate    => True_Term,
            Include_Type_Inv => Include_Type_Inv,
            Params           => Params,
            Use_Pred         => Use_Pred,
            New_Preds_Module => New_Preds_Module,
            T                => T_Comp,
            Loc_Incompl_Acc  => Loc_Incompl_Acc,
            New_Incompl_Acc  => New_Incompl_Acc,
            Expand_Incompl   => Expand_Incompl);

         return T_Comp;
      end Invariant_For_Comp;

      function Invariant_For_Array is new Build_Predicate_For_Array
        (Invariant_For_Comp);

      function Invariant_For_Record is new Build_Predicate_For_Record
        (Invariant_For_Comp, Invariant_For_Comp);

      --  If Ty's fullview is in SPARK, go to its underlying type to check its
      --  kind.

      Ty_Spec   : constant Entity_Id :=
        (if Is_Class_Wide_Type (Ty) then Get_Specific_Type_From_Classwide (Ty)
         else Ty);
      Ty_Ext    : constant Entity_Id := Retysp (Ty_Spec);

      Variables : Flow_Id_Sets.Set;

   --  Start of processing for Compute_Dynamic_Invariant

   begin
      --  If Use_Pred is true, then we already have generated a predicate
      --  for the dynamic invariant of elements of type Ty_Ext, except if the
      --  type is an itype or if it is standard boolean. We also avoid using
      --  the predicate for objects in split form as it would introduce an
      --  unnecessary conversion harmful to provers.

      if Use_Pred
        and then not Is_Itype (Ty_Ext)
        and then not Is_Standard_Boolean_Type (Ty_Ext)
        and then Eq_Base (Type_Of_Node (Ty_Ext), Get_Type (+Expr))
      then
         Variables_In_Dynamic_Invariant (Ty_Ext, Variables);

         declare
            Vars  : constant W_Expr_Array :=
              Get_Args_From_Variables (Variables, Params.Ref_Allowed);
            Num_B : constant Positive := 5 + Vars'Length;
            Args  : W_Expr_Array (1 .. Num_B);

         begin
            Args (1) := +Expr;
            Args (2) := +Initialized;
            Args (3) := +Only_Var;
            Args (4) := +Top_Predicate;
            Args (5) := +Include_Type_Inv;
            Args (6 .. Num_B) := Vars;

            T := New_Call (Name => E_Symb (E => Ty_Ext,
                                             S => WNE_Dynamic_Invariant),
                             Args => Args,
                             Typ  => EW_Bool_Type);
            return;
         end;
      end if;

      --  Dynamic property of the type itself

      if Type_Is_Modeled_As_Base (Ty_Ext)
        or else (Use_Split_Form_For_Type (Ty_Ext)
                 and then Get_Type_Kind (Get_Type (+Expr)) /= EW_Abstract)
      then
         T := +New_Dynamic_Property
           (Domain => EW_Pred,
            Ty     => Ty_Ext,
            Expr   => +Expr,
            Params => Params);

         --  If a scalar variable is not initialized, then its dynamic property
         --  may be false. As initialization is checked separately by flow
         --  analysis, we can assume that the variable is in bound as long as
         --  it does not introduce any unsoundness (the range is not empty).

         if T /= True_Pred then
            declare
               Why_Rep_Type : constant W_Type_Id := Base_Why_Type (Ty_Ext);
               Le_Op        : constant W_Identifier_Id :=
                 (if Why_Type_Is_Float (Why_Rep_Type) then
                       MF_Floats (Why_Rep_Type).Le
                  elsif Why_Type_Is_BitVector (Why_Rep_Type) then
                    MF_BVs (Why_Rep_Type).Ule
                  else Int_Infix_Le);
               First        : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain   => EW_Term,
                    Expr     => New_Attribute_Expr
                      (Ty       => Ty_Ext,
                       Domain   => EW_Term,
                       Attr     => Attribute_First,
                       Params   => Params),
                    To       => Why_Rep_Type);
               Last        : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain   => EW_Term,
                    Expr     => New_Attribute_Expr
                      (Ty     => Ty_Ext,
                       Domain => EW_Term,
                       Attr   => Attribute_Last,
                       Params => Params),
                    To       => Why_Rep_Type);
               Fst_Le_Last  : constant W_Pred_Id :=
                 New_Call (Name     => Le_Op,
                           Typ      => EW_Bool_Type,
                           Args     => (First, Last));
               Init_Flag    : constant W_Pred_Id :=
                 (if Is_Init_Wrapper_Type (Get_Type (+Expr))
                  then +Compute_Is_Initialized
                    (E                       => Ty_Ext,
                     Name                    => +Expr,
                     Ref_Allowed             => Params.Ref_Allowed,
                     Domain                  => EW_Pred,
                     Exclude_Always_Relaxed  => True)
                  else Pred_Of_Boolean_Term (W => Initialized));
            begin
               T := +W_Expr_Id'
                 (New_Conditional
                    (Domain      => EW_Pred,
                     Condition   =>
                       New_Or_Else_Expr
                         (+Init_Flag, +Fst_Le_Last, EW_Pred),
                     Then_Part   => +T,
                     Typ         => EW_Bool_Type));
            end;
         end if;
      elsif Is_Access_Type (Ty_Ext) and then Can_Never_Be_Null (Ty_Ext) then
         T := New_Not (Right => New_Pointer_Is_Null_Access (E    => Ty_Ext,
                                                            Name => +Expr));

      --  Do not assume bounds of arrays and discriminants if Only_Var is
      --  statically True.

      elsif Is_True_Boolean (+Only_Var) then
         T := True_Pred;
      elsif Is_Array_Type (Ty_Ext)
        and then not Is_Static_Array_Type (Ty_Ext)
      then
         T := +New_Dynamic_Property (Domain => EW_Pred,
                                     Ty     => Ty_Ext,
                                     Expr   => +Expr,
                                     Params => Params);

         --  For arrays, also assume the value of its bounds

         if Is_Constrained (Ty_Ext) then
            declare
               Index : Node_Id := First_Index (Ty_Ext);
               I     : Positive := 1;
            begin
               while Present (Index) loop
                  declare
                     Rng       : constant Node_Id := Get_Range (Index);
                     Rng_Ty    : constant W_Type_Id :=
                           Base_Why_Type_No_Bool (Etype (Index));
                     Low_Expr  : constant W_Expr_Id :=
                       Transform_Expr (Low_Bound (Rng), Rng_Ty,
                                       EW_Term, Params);
                     First_Eq  : constant W_Pred_Id :=
                       New_Call
                         (Name => Why_Eq,
                          Typ  => EW_Bool_Type,
                          Args =>
                            (1 => Insert_Conversion_To_Rep_No_Bool
                               (EW_Term,
                                +Get_Array_Attr
                                  (Domain => EW_Term,
                                   Expr   => +Expr,
                                   Attr   => Attribute_First,
                                   Dim    => I)),
                             2 => Low_Expr));
                     High_Expr : constant W_Expr_Id :=
                       Transform_Expr (High_Bound (Rng), Rng_Ty,
                                       EW_Term, Params);
                     Last_Eq   : constant W_Pred_Id :=
                       New_Call
                         (Name => Why_Eq,
                          Typ  => EW_Bool_Type,
                          Args =>
                            (1 => Insert_Conversion_To_Rep_No_Bool
                               (EW_Term,
                                +Get_Array_Attr
                                  (Domain => EW_Term,
                                   Expr   => +Expr,
                                   Attr   => Attribute_Last,
                                   Dim    => I)),
                             2 => High_Expr));
                  begin

                     --  Assuming the value of Ty's bounds

                     T := +New_And_Then_Expr
                       (Left   => +T,
                        Right  =>
                          +New_And_Then_Expr (Left   => +First_Eq,
                                              Right  => +Last_Eq,
                                              Domain => EW_Pred),
                        Domain => EW_Pred);

                  end;
                  Next_Index (Index);
                  I := I + 1;
               end loop;
            end;
         end if;

         T := New_Conditional
           (Condition => +Only_Var,
            Then_Part => +True_Pred,
            Else_Part => +T,
            Typ       => EW_Bool_Type);

      elsif Count_Discriminants (Ty_Ext) > 0
        and then Is_Constrained (Ty_Ext)
      then
         T := New_Conditional
           (Condition => +Only_Var,
            Then_Part => +True_Pred,
            Else_Part => +New_Dynamic_Property (Domain => EW_Pred,
                                                Ty     => Ty_Ext,
                                                Expr   => +Expr,
                                                Params => Params),
            Typ       => EW_Bool_Type);
      else
         T := True_Pred;
      end if;

      --  Add possible dynamic predicate. If the type defines at least partial
      --  default initialization, the predicate is checked at default
      --  initialization so it can be assumed to always hold. Otherwise, the
      --  predicate is only valid for initialized data. In all cases, only
      --  assume the predicate of the type itself when the top predicate should
      --  be included. Otherwise, assume the predicate of the first ancestor
      --  only.

      declare
         Typ_Pred              : constant W_Pred_Id :=
           Compute_Dynamic_Predicate (Expr, Ty_Ext, Params, Use_Pred => False);
         Anc_Ty                : constant Entity_Id :=
           Retysp (Etype (Ty_Ext));
         Anc_Typ_Pred          : constant W_Pred_Id :=
           (if Anc_Ty = Ty_Ext then True_Pred
            else Compute_Dynamic_Predicate
              (Expr, Anc_Ty, Params, Use_Pred => False));
         Pred_Check_At_Default : constant Boolean :=
           Default_Initialization (Ty_Ext) /= No_Default_Initialization;
         Init_Flag             : constant W_Pred_Id :=
           (if Is_Init_Wrapper_Type (Get_Type (+Expr))
            then +Compute_Is_Initialized
              (E                       => Ty_Ext,
               Name                    => +Expr,
               Ref_Allowed             => Params.Ref_Allowed,
               Domain                  => EW_Pred,
               Exclude_Always_Relaxed  => True)
            else Pred_Of_Boolean_Term (Initialized));
         Check_Pred            : constant W_Pred_Id :=
           New_Conditional
             (Condition => +Top_Predicate,
              Then_Part =>
                (if Pred_Check_At_Default then +Typ_Pred
                 else New_Conditional (Domain    => EW_Pred,
                                       Condition => +Init_Flag,
                                       Then_Part => +Typ_Pred,
                                       Typ       => EW_Bool_Type)),
              Else_Part =>
                (if Pred_Check_At_Default then +Anc_Typ_Pred
                 else New_Conditional (Domain    => EW_Pred,
                                       Condition => +Init_Flag,
                                       Then_Part => +Anc_Typ_Pred,
                                       Typ       => EW_Bool_Type)),
              Typ       => EW_Bool_Type);

      begin
         if Typ_Pred /= True_Pred then
            T := +New_And_Then_Expr (Left   => +T,
                                     Right  => +Check_Pred,
                                     Domain => EW_Pred);
         end if;
      end;

      --  Add possible type invariant. Only include type invariants that are
      --  defined outside the current compilation unit. Only deal with the
      --  top-level invariants as invariants of components will be added in
      --  recursive calls.

      declare
         Type_Inv : constant W_Pred_Id :=
           Compute_Type_Invariant
             (Expr, Ty_Ext, Params,
              On_External  => True,
              Include_Comp => False,
              Use_Pred     => Use_Pred);
      begin
         if not Is_True_Boolean (+Type_Inv) then
            T := +New_And_Then_Expr
              (Left   => +T,
               Right  => New_Conditional (Domain    => EW_Pred,
                                          Condition => +Include_Type_Inv,
                                          Then_Part => +Type_Inv,
                                          Typ       => EW_Bool_Type),
               Domain => EW_Pred);
         end if;
      end;

      --  Compute dynamic invariant for its components

      if Is_Array_Type (Ty_Ext)
        and then Ekind (Ty_Ext) /= E_String_Literal_Subtype
      then

         --  Generates:
         --  forall i1 .. in : int. in_range i1 /\ .. /\ in_range in ->
         --    Dynamic_Invariant (get <Expr> i1 .. in)

         T := +New_And_Then_Expr
           (Left   => +T,
            Right  => +Invariant_For_Array (Expr, Ty_Ext),
            Domain => EW_Pred);

      elsif Is_Record_Type (Ty_Ext)
        or else Is_Private_Type (Ty_Ext)
        or else Is_Concurrent_Type (Ty_Ext)
      then

         --  Generates:
         --  (check_for_f1 <Expr> -> Dynamic_Invariant <Expr>.rec__f1)
         --  /\ .. /\ (check_for_fn <Expr> -> Dynamic_Invariant <Expr>.rec__fn)
         --  As discriminants may occur in bounds of types of other fields,
         --  store them in the Symbol_Table.

         T := +New_And_Then_Expr
           (Left   => +T,
            Right  => +Invariant_For_Record (Expr, Ty_Ext),
            Domain => EW_Pred);

      elsif Is_Access_Type (Ty_Ext)
        and then Type_Needs_Dynamic_Invariant
          (Directly_Designated_Type (Ty_Ext))
      then

         --  For types designating an incomplete type, we cannot always assume
         --  the dynamic property of the designated type as they may be
         --  recursive. If Expand_Incompl is false, we use specific dynamic
         --  predicates stored in Incompl_Access_Dyn_Inv_Map. If there is no
         --  such predicate and New_Preds_Module is not empty, generate a new
         --  temp for them and store them inside New_Incompl_Acc. Otherwise,
         --  emit an info message to state that we may be missing some
         --  information. Usually, the first time a dynamic predicate will
         --  be computed for a type, it will be declared, so
         --  New_Preds_Module should not be empty and predicates will be
         --  created which can be reused later. The fall back case might happen
         --  for Itypes for which we do not generate a predicate.

         if Designates_Incomplete_Type (Repr_Pointer_Type (Ty_Ext))
           and then not Expand_Incompl
         then

            --  Search the dynamic invariant for Ty_Ext in the local maps first
            --  so that we get the local name if there is one.

            declare
               use Ada_To_Why_Ident;
               Dyn_Inv_Pos : Ada_To_Why_Ident.Cursor :=
                 Loc_Incompl_Acc.Find (Repr_Pointer_Type (Ty_Ext));
               Inserted    : Boolean;

            begin
               pragma Assert
                 (not (Has_Element (Dyn_Inv_Pos)
                  and then New_Incompl_Acc.Contains
                    (Repr_Pointer_Type (Ty_Ext))));

               if not Has_Element (Dyn_Inv_Pos) then
                  Dyn_Inv_Pos := New_Incompl_Acc.Find
                    (Repr_Pointer_Type (Ty_Ext));

                  --  Search in the global map

                  if not Has_Element (Dyn_Inv_Pos) then
                     Dyn_Inv_Pos := Incompl_Access_Dyn_Inv_Map.Find
                       (Repr_Pointer_Type (Ty_Ext));

                     --  If it was not found and we are allowed to introduce
                     --  new declarations (New_Preds_Module is set), introduce
                     --  it. We store it both inside Incompl_Access_Dyn_Inv_Map
                     --  and inside New_Incompl_Acc for further treatment.

                     if not Has_Element (Dyn_Inv_Pos)
                       and then New_Preds_Module /= Why_Empty
                     then
                        declare
                           Pred_Name : constant W_Identifier_Id :=
                             New_Identifier
                               (Name      => New_Temp_Identifier
                                  (Base_Name => "dynamic_invariant"),
                                Module    => New_Preds_Module,
                                Typ       => EW_Bool_Type);
                        begin
                           Incompl_Access_Dyn_Inv_Map.Insert
                             (Repr_Pointer_Type (Ty_Ext), Pred_Name);
                           New_Incompl_Acc.Insert
                             (Repr_Pointer_Type (Ty_Ext), To_Local (Pred_Name),
                              Dyn_Inv_Pos, Inserted);
                        end;
                     end if;
                  end if;
               end if;

               --  If we have a predicate, call it

               if Has_Element (Dyn_Inv_Pos) then
                  Variables_In_Dynamic_Invariant
                    (Directly_Designated_Type (Ty_Ext), Variables);

                  declare
                     Vars  : constant W_Expr_Array :=
                       Get_Args_From_Variables (Variables, Params.Ref_Allowed);
                     Num_B : constant Positive := 5 + Vars'Length;
                     Args  : W_Expr_Array (1 .. Num_B);

                  begin
                     Args (1) := +Expr;
                     Args (2) := +Initialized;
                     Args (3) := +Only_Var;
                     Args (4) := +Top_Predicate;
                     Args (5) := +Include_Type_Inv;
                     Args (6 .. Num_B) := Vars;
                     T := +New_And_Then_Expr
                       (Left        => +T,
                        Right       =>
                          New_Call (Name   => Element (Dyn_Inv_Pos),
                                    Args   => Args,
                                    Typ    => EW_Bool_Type,
                                    Domain => EW_Pred),
                        Domain      => EW_Pred);
                  end;

               --  If we have no predicate for Ty_Ext, we drop the predicate of
               --  the designated type. Warn the user if --info is set.

               elsif Debug.Debug_Flag_Underscore_F then
                  Error_Msg_N
                    ("info: ?subtype constraints on designated type not" &
                       " available for proof", Ty_Ext);
               end if;
            end;
         else
            T := +New_And_Then_Expr
              (Left   => +T,
               Right  => +Invariant_For_Access (+Expr, Ty_Ext),
               Domain => EW_Pred);
         end if;
      end if;
   end Compute_Dynamic_Invariant;

   -------------------------------
   -- Compute_Dynamic_Predicate --
   -------------------------------

   function Compute_Dynamic_Predicate
     (Expr     : W_Term_Id;
      Ty       : Entity_Id;
      Params   : Transformation_Params := Body_Params;
      Use_Pred : Boolean := True) return W_Pred_Id
   is
      Rep_Ty : Entity_Id := Retysp (Ty);
      Res    : W_Pred_Id := True_Pred;

   begin
      --  Go through the ancestors of Ty to collect all applicable predicates

      while Has_Predicates (Rep_Ty) loop
         declare
            Pred_Type : constant Entity_Id :=
              Get_Type_With_Predicate_Function (Rep_Ty);
            Pred_Fun  : constant Entity_Id := Predicate_Function (Pred_Type);

         begin
            --  If Use_Pred is true, then we already have generated a predicate
            --  for the dynamic predicate of elements of type Pred_Type. We
            --  also avoid using the predicate for objects in split form as it
            --  would introduce an unnecessary conversion harmful to provers.

            if Use_Pred
              and then Eq_Base (Type_Of_Node (Pred_Type), Get_Type (+Expr))
            then
               return +New_And_Then_Expr
                 (Left   => +New_Predicate_Call (Pred_Type, Expr, Params),
                  Right  => +Res,
                  Domain => EW_Pred);
            elsif Entity_In_SPARK (Pred_Fun) then
               declare
                  My_Params : Transformation_Params := Params;
               begin
                  My_Params.Gen_Marker := GM_Node_Only;
                  Res := +New_And_Then_Expr
                    (Left   => +Dynamic_Predicate_Expression
                       (Expr      => +Expr,
                        Pred_Subp => Pred_Fun,
                        Domain    => EW_Pred,
                        Params    => My_Params),
                     Right  => +Res,
                     Domain => EW_Pred);
               end;
            end if;

            --  Go directly to the first type on which the predicate applies
            --  using the type of the first formal of the predicate function.

            Rep_Ty := Retysp
              (Etype (First_Formal (Pred_Fun)));
         end;

         --  Go to the next type in the derivation tree of Rep_Ty to continue
         --  the search.

         declare
            Decl    : constant Node_Id := Enclosing_Declaration (Rep_Ty);
            Sub_Ty  : constant Node_Id :=
              (if Nkind (Decl) = N_Subtype_Declaration
               then Subtype_Indication (Decl)
               else Empty);
            --  If Rep_Ty is a subtype, we need to use its declaration to find
            --  the next subtype in the derivation tree. Indeed, Etype on
            --  subtypes returns the base type.

            Next_Ty : constant Entity_Id :=
              (if Present (Sub_Ty)
               then Retysp
                 (Entity
                      (if Nkind (Sub_Ty) = N_Subtype_Indication
                       then Subtype_Mark (Sub_Ty)
                       else Sub_Ty))
               else Retysp (Etype (Rep_Ty)));
         begin
            exit when Next_Ty = Rep_Ty;
            Rep_Ty := Next_Ty;
         end;
      end loop;
      return Res;
   end Compute_Dynamic_Predicate;

   -------------------
   -- Compute_Store --
   -------------------

   procedure Compute_Store
     (Pattern        : Item_Type;
      Actual         : Node_Id;
      Need_Store     : Boolean;
      No_Pred_Checks : Boolean;
      Pre_Expr       : W_Expr_Id;
      Store          : W_Statement_Sequence_Unchecked_Id;
      Params         : Transformation_Params)
   is
   begin
      --  If needed, recompute the actual expression and store it in Actual

      if Need_Store then
         declare
            Reconstructed_Arg : constant W_Prog_Id :=
              Reconstruct_Expr_From_Item
                (Pattern   => Pattern,
                 Actual    => Actual,
                 No_Checks => False,
                 Pre_Expr  => Pre_Expr);

         begin
            Statement_Sequence_Append_To_Statements
              (Store, New_Assignment
                 (Ada_Node => Actual,
                  Lvalue   => Actual,
                  Expr     => Reconstructed_Arg));
         end;
      end if;

      --  Handle the initialization flag on the actual if any

      if Present (Actual) and then Is_Simple_Actual (Actual) then
         declare
            Actual_Binder : constant Item_Type :=
              Ada_Ent_To_Why.Element
                (Symbol_Table, Entity (Actual));

         begin
            if Actual_Binder.Init.Present then

               --  Assign the initialization flag if any. The parameter has
               --  been initialized.

               Statement_Sequence_Append_To_Statements
                 (Store,
                  New_Assignment
                    (Ada_Node => Actual,
                     Name     => Actual_Binder.Init.Id,
                     Value    => True_Prog,
                     Typ      => EW_Bool_Type,
                     Labels   => Symbol_Sets.Empty_Set));
            end if;
         end;
      end if;

      --  If discriminants are mutable we need to assume preservation
      --  of the discriminants if the actual is constrained.

      if Pattern.Kind = DRecord
        and then Pattern.Discrs.Present
        and then Pattern.Discrs.Binder.Mutable
      then
         declare
            Discr_Name  : constant W_Identifier_Id :=
              Pattern.Discrs.Binder.B_Name;
            Assumption  : W_Expr_Id;
         begin

            --  If the formal has mutable discriminants,
            --  store in Assumption that its discriminants
            --  cannot have been modified if the actual is
            --  constrained.

            Assumption :=
              New_Call
                (Domain => EW_Pred,
                 Typ    => EW_Bool_Type,
                 Name   => Why_Eq,
                 Args   =>
                   (1 => New_Deref
                      (Right => Discr_Name,
                       Typ   => Get_Typ (Discr_Name)),
                    2 => New_Discriminants_Access
                      (Domain => EW_Prog,
                       Name   => Pre_Expr,
                       Ty     => Pattern.Typ)));

            Assumption :=
              New_Conditional
                (Domain      => EW_Pred,
                 Condition   =>
                   New_Constrained_Attribute_Expr
                     (Domain => EW_Term,
                      Prefix => Actual),
                 Then_Part   => Assumption);

            Statement_Sequence_Append_To_Statements
              (Store, New_Assume_Statement (Pred => +Assumption));
         end;
      end if;

      --  If needed, perform the check for a dynamic predicate and null
      --  exclusion of access types on OUT and
      --  IN OUT parameters on return from the call. This check is not done
      --  as part of the conversion from formal to actual parameter, as
      --  the check done in conversions also involves invariant properties
      --  of the type (array bounds, record discriminants, etc.). Thus,
      --  conversion is done with Insert_Simple_Conversion in domain
      --  EW_Pterm, which does not introduce checks, and the required
      --  check for dynamic predicate is introduced here.

      --  The case of scalar types is different, as the conversion from
      --  formal to actual on OUT and IN OUT parameters is performed with
      --  checks, using Insert_Checked_Conversion in domain EW_Prog, so do
      --  not repeat the check here.

      declare
         Need_Pred_Check_On_Store : constant Boolean :=
            not No_Pred_Checks
           and then not Is_Scalar_Type (Retysp (Etype (Actual)))
           and then Item_Is_Mutable (Pattern);
      begin
         if Present (Actual)
           and then Need_Pred_Check_On_Store
         then
            declare
               Postfetch_Actual : constant W_Prog_Id :=
                 +Transform_Expr (Actual, EW_Pterm, Params);

            begin
               --  Generate a predicate check if the actual has a predicate

               if Has_Predicates (Retysp (Etype (Actual))) then
                  Statement_Sequence_Append_To_Statements
                    (Store, New_Predicate_Check (Actual, Etype (Actual),
                     +Postfetch_Actual));
               end if;

               --  Generate a null exclusion check if the actual cannot be
               --  null but the formal can.

               if Is_Access_Type (Retysp (Etype (Actual)))
                 and then Can_Never_Be_Null (Retysp (Etype (Actual)))
                 and then not
                   Can_Never_Be_Null (Get_Ada_Type_From_Item (Pattern))
               then
                  Statement_Sequence_Append_To_Statements
                    (Store,
                     New_Binding
                       (Ada_Node => Actual,
                        Name     => New_Identifier
                          (Domain => EW_Prog,
                           Name   => "_",
                           Typ    => Get_Type (+Postfetch_Actual)),
                        Def      => New_VC_Call
                          (Ada_Node => Actual,
                           Name     => To_Program_Space
                             (E_Symb (Etype (Actual),
                              WNE_Assign_Null_Check)),
                           Progs    => (1 => +Postfetch_Actual),
                           Domain   => EW_Prog,
                           Reason   => VC_Null_Exclusion,
                           Typ      => Get_Type (+Postfetch_Actual)),
                        Context  => +Void,
                        Typ      => EW_Unit_Type));
               end if;
            end;
         end if;
      end;
   end Compute_Store;

   -------------------------------
   -- Compute_Is_Moved_Property --
   -------------------------------

   function Compute_Is_Moved_Property
     (Expr     : W_Term_Id;
      Ty       : Entity_Id;
      Use_Pred : Boolean := True) return W_Pred_Id
   is
      --  Local subprograms

      function Is_Moved_For_Comp
        (C_Expr : W_Term_Id;
         C_Ty   : Entity_Id;
         E      : Entity_Id)
         return W_Pred_Id;

      function Is_Moved_For_Comp
        (C_Expr : W_Term_Id;
         C_Ty   : Entity_Id)
         return W_Pred_Id
      is
        (Is_Moved_For_Comp (C_Expr, C_Ty, Empty));

      ----------------------
      -- Is_Moved_For_Comp --
      ----------------------

      function Is_Moved_For_Comp
        (C_Expr : W_Term_Id;
         C_Ty   : Entity_Id;
         E      : Entity_Id)
         return W_Pred_Id
      is
         pragma Unreferenced (E);
      begin
         if Is_Deep (C_Ty) then
            return Compute_Is_Moved_Property (C_Expr, C_Ty);
         else
            return True_Pred;
         end if;
      end Is_Moved_For_Comp;

      function Is_Moved_For_Array is new Build_Predicate_For_Array
        (Is_Moved_For_Comp);

      function Is_Moved_For_Record is new Build_Predicate_For_Record
        (Is_Moved_For_Comp, Is_Moved_For_Comp);

   --  Start of processing for Compute_Is_Moved_Property

   begin
      if Has_Access_Type (Ty) then
         return +New_Or_Expr
           (Left   => New_Pointer_Is_Null_Access (Ty, +Expr),
            Right  => New_Pointer_Is_Moved_Access (Ty, +Expr),
            Domain => EW_Pred);

      elsif Use_Pred then
         declare
            --  We need to convert to the expected type for unconstrained
            --  arrays in split form.

            Full_Expr : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain         => EW_Term,
                 Expr           => +Expr,
                 To             => EW_Abstract (Ty),
                 Force_No_Slide => True);
         begin
            return +W_Expr_Id'(New_Call
                               (Domain => EW_Pred,
                                Name   => E_Symb (Ty, WNE_Is_Moved),
                                Args   => (1 => Full_Expr),
                                Typ    => EW_Bool_Type));
         end;

      elsif Has_Record_Type (Ty) then
         return Is_Moved_For_Record (Expr, Ty);

      else
         pragma Assert (Has_Array_Type (Ty));
         return Is_Moved_For_Array (Expr, Ty);
      end if;
   end Compute_Is_Moved_Property;

   ----------------------------
   -- Compute_Moved_Relation --
   ----------------------------

   function Compute_Moved_Relation
     (Expr1    : W_Term_Id;
      Expr2    : W_Term_Id;
      Ty       : Entity_Id;
      Use_Pred : Boolean := True) return W_Pred_Id
   is
      --  Local subprograms

      function Set_Moved_For_Comp
        (C_Expr1 : W_Term_Id;
         C_Expr2 : W_Term_Id;
         C_Ty   : Entity_Id;
         E      : Entity_Id)
         return W_Pred_Id;

      function Set_Moved_For_Comp
        (C_Expr1 : W_Term_Id;
         C_Expr2 : W_Term_Id;
         C_Ty    : Entity_Id)
         return W_Pred_Id
      is
        (Set_Moved_For_Comp (C_Expr1, C_Expr2, C_Ty, Empty));

      ------------------------
      -- Set_Moved_For_Comp --
      ------------------------

      function Set_Moved_For_Comp
        (C_Expr1 : W_Term_Id;
         C_Expr2 : W_Term_Id;
         C_Ty    : Entity_Id;
         E       : Entity_Id)
         return W_Pred_Id
      is
         pragma Unreferenced (E);
      begin
         if Is_Deep (C_Ty) then
            return Compute_Moved_Relation (C_Expr1, C_Expr2, C_Ty);
         else
            return +New_Comparison
              (Symbol => Why_Eq,
               Domain => EW_Pred,
               Left   => +C_Expr1,
               Right  => +C_Expr2);
         end if;
      end Set_Moved_For_Comp;

      function Set_Moved_For_Array is new Build_Binary_Predicate_For_Array
        (Set_Moved_For_Comp);

      function Build_Equality_For_Discr
        (D_Expr1, D_Expr2 : W_Term_Id; D_Ty : Entity_Id; Dummy_E : Entity_Id)
         return W_Pred_Id
      is (+New_Ada_Equality (Typ    => D_Ty,
                             Domain => EW_Pred,
                             Left   => +D_Expr1,
                             Right  => +D_Expr2));

      function Set_Moved_For_Record is new Build_Binary_Predicate_For_Record
        (Build_Equality_For_Discr, Set_Moved_For_Comp);

   --  Start of processing for Compute_Moved_Relation

   begin
      if Has_Access_Type (Ty) then
         return +New_Comparison
           (Symbol => Why_Eq,
            Left   => New_Pointer_Is_Moved_Access (Ty, +Expr1),
            Right  => +True_Term,
            Domain => EW_Pred);

      --  We only introduce a predicate for composite types. In that case, call
      --  the predicate when Use_Pred is True.

      elsif Use_Pred then
         return +W_Expr_Id'(New_Call
                            (Domain => EW_Pred,
                             Name   => E_Symb (Ty, WNE_Moved_Relation),
                             Args   => (1 => +Expr1, 2 => +Expr2),
                             Typ    => EW_Bool_Type));

      elsif Has_Record_Type (Ty) then
         return Set_Moved_For_Record (Expr1, Expr2, Ty);

      else
         pragma Assert (Has_Array_Type (Ty));
         return Set_Moved_For_Array (Expr1, Expr2, Ty);
      end if;
   end Compute_Moved_Relation;

   -----------------------
   -- Compute_Tag_Check --
   -----------------------

   function Compute_Tag_Check
     (Call   : Node_Id;
      Params : Transformation_Params) return W_Prog_Id
   is
      Controlling_Arg : constant Node_Id :=
        (if Nkind (Call) = N_Entry_Call_Statement
         then Empty
         else Controlling_Argument (Call));
      Control_Tag     : W_Expr_Id := Why_Empty;
      Check           : W_Pred_Id := True_Pred;
      Needs_Check     : Boolean := False;

      procedure One_Param (Formal : Entity_Id; Actual : Node_Id) with
        Pre  => Needs_Check = Present (Control_Tag),
        Post => Needs_Check = Present (Control_Tag);
         --  Compute a Why expression for each parameter

      ---------------
      -- One_Param --
      ---------------

      procedure One_Param (Formal : Entity_Id; Actual : Node_Id) is
         pragma Unreferenced (Formal);
         New_Check : W_Pred_Id;
      begin
         if not Is_Controlling_Actual (Actual)
           or else Actual = Controlling_Arg
         then
            return;
         end if;

         --  We have found a controlling argument different from the first one.
         --  We need a check. If it's the first time we come here, we need to
         --  compute the reference tag first

         if not Needs_Check then
            Needs_Check := True;
            declare
               Tmp : constant W_Expr_Id :=
                 Transform_Expr (Controlling_Arg, EW_Term, Params);
            begin
               Control_Tag :=
                 New_Tag_Access
                   (Ada_Node => Controlling_Arg,
                    Domain   => EW_Term,
                    Name     => Tmp,
                    Ty       => Get_Ada_Node (+Get_Type (Tmp)));
            end;
         end if;
         declare
            Tmp : constant W_Expr_Id :=
              Transform_Expr (Actual, EW_Term, Params);
         begin
            New_Check :=
              New_Call
                (Name => Why_Eq,
                 Typ  => EW_Bool_Type,
                 Args =>
                   (1 => Control_Tag,
                    2 =>
                      New_Tag_Access
                        (Name     => Tmp,
                         Ada_Node => Actual,
                         Domain   => EW_Term,
                         Ty       => Get_Ada_Node (+Get_Type (Tmp)))));
         end;

         Check :=
           +New_And_Expr
           (Domain => EW_Pred,
            Left   => +Check,
            Right  => +New_Check);
      end One_Param;

      procedure Iterate_Call is new Iterate_Call_Parameters (One_Param);

   --  Start of processing for Compute_Tag_Check

   begin
      if No (Controlling_Arg) then
         return +Void;
      end if;

      Iterate_Call (Call);
      if Needs_Check then
         return
           New_Located_Assert
             (Ada_Node => Call,
              Pred     => Check,
              Reason   => VC_Tag_Check,
              Kind     => EW_Assert);
      else
         return +Void;
      end if;
   end Compute_Tag_Check;

   --------------------------------------
   -- Compute_Top_Level_Type_Invariant --
   --------------------------------------

   function Compute_Top_Level_Type_Invariant
     (Expr     : W_Term_Id;
      Ty       : Entity_Id;
      Params   : Transformation_Params := Body_Params;
      Use_Pred : Boolean := True) return W_Pred_Id
   is
      --  If Ty's fullview is in SPARK, go to its underlying type to check its
      --  kind.

      Rep_Ty : constant Entity_Id := Retysp (Ty);

   begin
      if Has_Invariants_In_SPARK (Rep_Ty) then

            --  If Use_Pred is true, then we already have generated a predicate
            --  for the type invariant of elements of type Ty. We also avoid
            --  using the predicate for objects in split form as it would
            --  introduce an unnecessary conversion harmful to provers.

            if Use_Pred
              and then Eq_Base (Type_Of_Node (Rep_Ty), Get_Type (+Expr))
            then
               return New_Type_Invariant_Call (Rep_Ty, Expr, Params);
            else
               return
                 +Type_Invariant_Expression
                 (Expr     => +Expr,
                  Inv_Subp => Invariant_Procedure (Rep_Ty),
                  Domain   => EW_Pred,
                  Params   => Params);
            end if;
      else
         return True_Pred;
      end if;
   end Compute_Top_Level_Type_Invariant;

   ----------------------------
   -- Compute_Type_Invariant --
   ----------------------------

   function Compute_Type_Invariant
     (Expr         : W_Term_Id;
      Ty           : Entity_Id;
      Params       : Transformation_Params := Body_Params;
      On_External  : Boolean := False;
      On_Internal  : Boolean := False;
      Include_Comp : Boolean := True;
      Use_Pred     : Boolean := True) return W_Pred_Id
   is
      function Invariant_For_Comp
        (C_Expr : W_Term_Id;
         C_Ty   : Entity_Id;
         E      : Entity_Id)
         return W_Pred_Id;
      --  @param C_Expr expression for a component
      --  @param C_Ty component type
      --  @param E not referenced
      --  @return predicate for individual components

      function Invariant_For_Comp
        (C_Expr : W_Term_Id;
         C_Ty   : Entity_Id)
         return W_Pred_Id
      is (Invariant_For_Comp (C_Expr, C_Ty, Empty));

      ------------------------
      -- Invariant_For_Comp --
      ------------------------

      function Invariant_For_Comp
        (C_Expr : W_Term_Id;
         C_Ty   : Entity_Id;
         E      : Entity_Id)
         return W_Pred_Id
      is
        (Compute_Type_Invariant
           (C_Expr, C_Ty, Params, On_External => On_External,
            On_Internal => On_Internal));

      function Invariant_For_Array is new Build_Predicate_For_Array
        (Invariant_For_Comp);

      function Invariant_For_Record is new Build_Predicate_For_Record
        (Invariant_For_Comp, Invariant_For_Comp);

      Rep_Ty : constant Entity_Id := Retysp (Ty);
      --  If Ty's fullview is in SPARK, go to its underlying type to check its
      --  kind.

      Pred : W_Pred_Id := True_Pred;

   --  Start of processing for Compute_Type_Invariant

   begin
      --  Check for invariants on the type and its ancestors

      declare
         Current : Entity_Id := Rep_Ty;
         Parent  : Entity_Id;
      begin
         loop
            if Has_Invariants_In_SPARK (Current)
              and then (if Has_Visible_Type_Invariants (Current)
                        then On_Internal
                        else On_External)
            then
               Pred := +New_And_Then_Expr
                 (Left   => +Pred,
                  Right  => +Compute_Top_Level_Type_Invariant
                    (+Insert_Simple_Conversion
                         (Domain         => EW_Term,
                          Expr           => +Expr,
                          To             => Type_Of_Node (Current),
                          Force_No_Slide => True), Current, Params,
                     Use_Pred => Use_Pred),
                  Domain   => EW_Pred);
            end if;

            Parent := Retysp (Etype (Current));
            exit when Current = Parent;
            Current := Parent;
         end loop;
      end;

      --  Check for invariants on components.

      if Include_Comp then

         --  For array types, produce:
         --  (forall i1, i2 .... in_range1 (i1) /\ inrange2 (i2) /\ ... ->
         --      invariant (a (i1, i2, ...)))

         if Is_Array_Type (Rep_Ty) then

            Pred := +New_And_Then_Expr
              (Left   => +Pred,
               Right  => +Invariant_For_Array (Expr, Rep_Ty),
               Domain => EW_Pred);

         --  For array record types, produce:
         --  invariant (r.d1) /\ ...
         --      /\ (check_for_f1 (r) -> invariant (r.f1)) /\ ...

         elsif Is_Private_Type (Rep_Ty)
           or else Is_Record_Type (Rep_Ty)
           or else Is_Concurrent_Type (Rep_Ty)
         then

            Pred := +New_And_Then_Expr
              (Left   => +Pred,
               Right  => +Invariant_For_Record (Expr, Rep_Ty),
               Domain => EW_Pred);
         end if;
      end if;

      return Pred;
   end Compute_Type_Invariant;

   ------------------------------
   -- Discrete_Choice_Is_Range --
   ------------------------------

   function Discrete_Choice_Is_Range (Choice : Node_Id) return Boolean is
      Is_Range : Boolean;
   begin
      case Nkind (Choice) is
         when N_Subtype_Indication
            | N_Range
         =>
            Is_Range := True;

         when N_Identifier
            | N_Expanded_Name
         =>
            if Is_Type (Entity (Choice)) then
               Is_Range := True;
            else
               Is_Range := False;
            end if;

         when N_Others_Choice =>
            Is_Range := True;

         when others =>
            Is_Range := False;
      end case;
      return Is_Range;
   end Discrete_Choice_Is_Range;

   ----------------------------------
   -- Dynamic_Predicate_Expression --
   ----------------------------------

   function Dynamic_Predicate_Expression
     (Expr      : W_Expr_Id;
      Pred_Subp : Entity_Id;
      Domain    : EW_Domain;
      Params    : Transformation_Params) return W_Expr_Id
   is
      Result     : W_Expr_Id;
      Pred_Expr  : constant Node_Id :=
        Get_Expr_From_Return_Only_Func (Pred_Subp);
      Pred_Param : constant Entity_Id := First_Formal (Pred_Subp);
      Pred_Id    : constant W_Identifier_Id :=
        New_Temp_Identifier (Pred_Param, Get_Type (+Expr));

   begin
      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      --  Register the temporary identifier Pred_Id for parameter Pred_Param in
      --  the symbol table. This ensures both that a distinct name is used each
      --  time (preventing name capture), and that the type of Expr is used as
      --  the type used to represent Pred_Param (avoiding type conversion).

      if Get_Type_Kind (Get_Type (+Expr)) = EW_Split
        and then Has_Array_Type (Get_Ada_Node (+Get_Type (+Expr)))
      then
         declare
            E : constant Item_Type :=
              Ada_Ent_To_Why.Element
                (Symbol_Table, Get_Entity_Of_Variable (+Expr));
         begin
            Insert_Item
              (I => Item_Type'(Kind    => UCArray,
                               Local   => E.Local,
                               Init    => <>,
                               Content =>
                                 Binder_Type'(B_Name => Pred_Id,
                                              others => <>),
                               Dim     => E.Dim,
                               Bounds  => E.Bounds),
               E => Pred_Param);
         end;
      else
         Insert_Entity (Pred_Param, Pred_Id);
      end if;

      --  Transform the predicate expression into Why3

      Result := +Transform_Expr (Expr   => Pred_Expr,
                                 Domain => Domain,
                                 Params => Params);

      --  Relate the name Pred_Id used in the predicate expression to the
      --  value Expr for which the predicate is checked.

      Result := New_Binding (Name    => Pred_Id,
                             Def     => +Expr,
                             Context => +Result,
                             Domain  => Domain,
                             Typ     => Get_Type (+Result));

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      return Result;
   end Dynamic_Predicate_Expression;

   -----------------------------
   -- Expected_Type_Of_Prefix --
   -----------------------------

   function Expected_Type_Of_Prefix (N : Node_Id) return Entity_Id is
   begin
      case Nkind (N) is
         --  The frontend may introduce an unchecked type conversion on the
         --  variable assigned to, in particular for inlining. Reach through
         --  the variable assigned in that case.

         when N_Unchecked_Type_Conversion =>
            return Expected_Type_Of_Prefix (Expression (N));

         when N_Type_Conversion =>
            return Expected_Type_Of_Prefix (Expression (N));

         when N_Identifier
            | N_Expanded_Name
            =>
            declare
               Ent : constant Entity_Id := Entity (N);
            begin
               if Is_Protected_Component_Or_Discr_Or_Part_Of (Ent) then
                  return Type_Of_Node (Etype (Ent));
               else
                  return Retysp (Get_Ada_Type_From_Item
                                 (Ada_Ent_To_Why.Element (Symbol_Table, Ent)));
               end if;
            end;

         when N_Slice =>
            return Etype (N);

         when N_Indexed_Component =>
            return Retysp
              (Component_Type (Expected_Type_Of_Prefix (Prefix (N))));

         when N_Selected_Component =>
            declare
               Pref : constant Entity_Id :=
                 Expected_Type_Of_Prefix (Prefix (N));
               Comp : constant Entity_Id :=
                 Search_Component_In_Type (Pref, Entity (Selector_Name (N)));
            begin
               return Retysp (Etype (Comp));
            end;

         when N_Explicit_Dereference =>
            return Etype (N);

         when others =>
            Ada.Text_IO.Put_Line ("[Expected_Type] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;
   end Expected_Type_Of_Prefix;

   function Expected_Type_Of_Prefix (N : Node_Id) return W_Type_Id is
      Init_Wrapper : constant Boolean := Expr_Has_Relaxed_Init (N);
   begin
      case Nkind (N) is
         --  The frontend may introduce an unchecked type conversion on the
         --  variable assigned to, in particular for inlining. Reach through
         --  the variable assigned in that case.

         when N_Unchecked_Type_Conversion =>
            return Expected_Type_Of_Prefix (Expression (N));

         when N_Type_Conversion =>
            return Expected_Type_Of_Prefix (Expression (N));

         when N_Identifier
            | N_Expanded_Name
         =>
            declare
               Ent : constant Entity_Id := Entity (N);
            begin
               if Is_Protected_Component_Or_Discr_Or_Part_Of (Ent) then
                  return Type_Of_Node (Etype (Ent));
               else
                  return Get_Why_Type_From_Item
                    (Ada_Ent_To_Why.Element (Symbol_Table, Ent));
               end if;
            end;

         when N_Slice | N_Indexed_Component | N_Selected_Component =>
            return
              EW_Abstract
                (Expected_Type_Of_Prefix (N), Relaxed_Init => Init_Wrapper);

         when N_Explicit_Dereference | N_Function_Call =>
            return
              EW_Abstract (Etype (N), Relaxed_Init => Init_Wrapper);

         when others =>
            Ada.Text_IO.Put_Line ("[Expected_Type] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;
   end Expected_Type_Of_Prefix;

   ------------------------
   -- Get_Item_From_Expr --
   ------------------------

   procedure Get_Item_From_Expr
     (Pattern     : Item_Type;
      Expr        : W_Expr_Id;
      Constr_Expr : W_Expr_Id := Why_Empty;
      Context     : in out Ref_Context;
      Args        : out W_Expr_Array;
      Need_Store  : out Boolean;
      Reuse_Discr : Boolean := False)
   is
      Count : Positive := Args'First;

   begin
      Need_Store := False;

      case Pattern.Kind is
         when Concurrent_Self | Regular =>

            --  We need to create a new reference if the binder is mutable

            if Pattern.Main.Mutable then
               Context.Append
                 (Ref_Type'(Mutable => True,
                            Name    => Pattern.Main.B_Name,
                            Value   => Expr));
               Args (Count) := +Pattern.Main.B_Name;
               Need_Store := True;

            --  Otherwise the expression is used as is

            else
               Args (Count) := Expr;
            end if;
            Count := Count + 1;

         when DRecord =>

            --  If the pattern has a component for fields, it is necessarily
            --  mutable so we need a reference for it.

            if Pattern.Fields.Present then
               pragma Assert (Pattern.Fields.Binder.Mutable);
               Context.Append
                 (Ref_Type'(Mutable => True,
                            Name    => Pattern.Fields.Binder.B_Name,
                            Value   =>
                              New_Fields_Access (Domain => EW_Prog,
                                                 Name   => Expr,
                                                 Ty     => Pattern.Typ)));
               Args (Count) := +Pattern.Fields.Binder.B_Name;
               Need_Store := True;
               Count := Count + 1;
            end if;

            --  We need a reference for discriminants if they are mutable. If
            --  Reuse_Discr is set to true, then the identifier from pattern
            --  can be used directly. Otherwise, we get the discriminant
            --  values from Expr.

            if Pattern.Discrs.Present
              and then Pattern.Discrs.Binder.Mutable
            then
               if not Reuse_Discr then
                  Context.Append
                    (Ref_Type'(Mutable => True,
                               Name    => Pattern.Discrs.Binder.B_Name,
                               Value   =>
                                 New_Discriminants_Access
                                   (Domain => EW_Prog,
                                    Name   => Expr,
                                    Ty     => Pattern.Typ)));
                  Need_Store := True;
               end if;
               Args (Count) := +Pattern.Discrs.Binder.B_Name;
               Count := Count + 1;

            elsif Pattern.Discrs.Present then
               if Reuse_Discr then
                  Args (Count) := +Pattern.Discrs.Binder.B_Name;
               else
                  Args (Count) := New_Discriminants_Access
                    (Domain   => EW_Prog,
                     Name     => Expr,
                     Ty       => Pattern.Typ);
               end if;
               Count := Count + 1;
            end if;

            --  For the Constr component, use the value of the 'Constrained
            --  attribute on the actual.

            if Pattern.Constr.Present then
               Args (Count) := Constr_Expr;
               Count := Count + 1;
            end if;

            if Pattern.Tag.Present then
               Args (Count) :=
                 New_Tag_Access
                   (Domain => EW_Prog,
                    Name   => Expr,
                    Ty     => Pattern.Typ);

               Count := Count + 1;
            end if;

         when UCArray =>

            --  The Content component of the pattern is necessarily mutable so
            --  we need a reference for it.

            pragma Assert (Pattern.Content.Mutable);

            Context.Append
              (Ref_Type'
                 (Mutable => True,
                  Name    => Pattern.Content.B_Name,
                  Value   =>
                    (if Has_Static_Array_Type (Get_Ada_Node (+Get_Type (Expr)))
                     or else Get_Type_Kind (Get_Type (Expr)) = EW_Split
                     then Expr
                     else Array_Convert_To_Base (Domain => EW_Prog,
                                                 Ar     => Expr))));
            Args (Count) := +Pattern.Content.B_Name;
            Need_Store := True;
            Count := Count + 1;

            --  We get the bounds from Expr

            for I in 1 .. Pattern.Dim loop
               Args (Count) :=
                 Insert_Simple_Conversion
                   (Domain   => EW_Prog,
                    Expr     => Get_Array_Attr (Domain => EW_Prog,
                                                Expr   => Expr,
                                                Attr   => Attribute_First,
                                                Dim    => I),
                    To       =>
                      Get_Typ (Pattern.Bounds (I).First));
               Args (Count + 1) :=
                 Insert_Simple_Conversion
                   (Domain   => EW_Prog,
                    Expr     => Get_Array_Attr (Domain => EW_Prog,
                                                Expr   => Expr,
                                                Attr   => Attribute_Last,
                                                Dim    => I),
                    To       =>
                      Get_Typ (Pattern.Bounds (I).Last));
               Count := Count + 2;
            end loop;

         when Pointer =>

            --  The Value component of the pattern is necessarily mutable so
            --  we need a reference for it.

            pragma Assert (Pattern.Value.Mutable);

            Context.Append
              (Ref_Type'
                 (Mutable => True,
                  Name    => Pattern.Value.B_Name,
                  Value   => New_Pointer_Value_Access
                    (Ada_Node => Empty,
                     Domain   => EW_Pterm,
                     E        => Etype (Pattern.Value.Ada_Node),
                     Name     => Expr)));
            Args (Count) := +Pattern.Value.B_Name;
            Need_Store := True;
            Count := Count + 1;

            --  If the address and is_null components are mutable, we also
            --  introduce new references for them. The initial value is taken
            --  from Expr.

            if Pattern.Mutable then
               Context.Append
                 (Ref_Type'
                    (Mutable => True,
                     Name    => Pattern.Address,
                     Value   => New_Pointer_Address_Access
                       (E    => Etype (Pattern.Value.Ada_Node),
                        Name => Expr)));
               Args (Count) := +Pattern.Address;
               Count := Count + 1;
               Context.Append
                 (Ref_Type'
                    (Mutable => True,
                     Name    => Pattern.Is_Null,
                     Value   => New_Pointer_Is_Null_Access
                       (E    => Etype (Pattern.Value.Ada_Node),
                        Name => Expr)));
               Args (Count) := +Pattern.Is_Null;
               Count := Count + 1;
            else
               Args (Count) :=
                 New_Pointer_Address_Access
                   (E    => Etype (Pattern.Value.Ada_Node),
                    Name => Expr);
               Count := Count + 1;
               Args (Count) :=
                 New_Pointer_Is_Null_Access
                   (E    => Etype (Pattern.Value.Ada_Node),
                    Name => Expr);
               Count := Count + 1;
            end if;

            --  We always need a new reference for is_moved

            Context.Append
              (Ref_Type'
                 (Mutable => True,
                  Name    => Pattern.Is_Moved,
                  Value   => New_Pointer_Is_Moved_Access
                    (E    => Etype (Pattern.Value.Ada_Node),
                     Name => Expr)));
            Args (Count) := +Pattern.Is_Moved;
            Count := Count + 1;

         when Func    =>
            raise Program_Error;
      end case;
   end Get_Item_From_Expr;

   -----------------------
   -- Get_Item_From_Var --
   -----------------------

   procedure Get_Item_From_Var
     (Pattern     : in out Item_Type;
      Var         : Item_Type;
      Expr        : W_Expr_Id;
      Constr_Expr : W_Expr_Id := Why_Empty;
      Context     : in out Ref_Context;
      Args        : out W_Expr_Array;
      Need_Store  : out Boolean)
   is
      Count : Positive := Args'First;

   begin
      Need_Store := False;

      case Pattern.Kind is
         when Concurrent_Self =>

            --  We can always reuse the reference for concurrent self

            Args (Count) := +Var.Main.B_Name;
            Count := Count + 1;

         when Regular =>

            --  We can reuse the reference of the actual if Pattern and Var
            --  have the same type.

            if Pattern.Main.Mutable
              and then Eq_Base (Get_Why_Type_From_Item (Pattern),
                                Get_Why_Type_From_Item (Var))
            then
               pragma Assert (Var.Kind = Regular and then Var.Main.Mutable);
               Args (Count) := +Var.Main.B_Name;

            --  Otherwise, a new temporary is needed

            else
               Get_Item_From_Expr
                 (Pattern     => Pattern,
                  Expr        => Expr,
                  Constr_Expr => Constr_Expr,
                  Context     => Context,
                  Args        => Args,
                  Need_Store  => Need_Store);
               return;
            end if;

         when DRecord =>
            pragma Assert (Var.Kind = DRecord);

            --  Try to reuse the Fields identifier from Var

            if Pattern.Fields.Present then
               pragma Assert (Pattern.Fields.Binder.Mutable);

               --  We can reuse the Fields identifier from Var if both types
               --  have the same fields and both are wrapper types or none.

               if Oldest_Parent_With_Same_Fields (Pattern.Typ)
                  = Oldest_Parent_With_Same_Fields (Var.Typ)
                 and then Is_Init_Wrapper_Type (Get_Why_Type_From_Item (Var))
                   = Is_Init_Wrapper_Type (Get_Why_Type_From_Item (Pattern))
               then
                  pragma Assert (Var.Fields.Present
                                 and then Var.Fields.Binder.Mutable);
                  Pattern.Fields := Var.Fields;
                  Args (Count) := +Var.Fields.Binder.B_Name;
                  Count := Count + 1;

               --  Otherwise, we revert to creating the identifiers from Expr.
               --  We can still reuse the variable for discriminants if both
               --  are similarly mutable.

               elsif Pattern.Discrs.Present
                 and then Pattern.Discrs.Binder.Mutable
                   = Var.Discrs.Binder.Mutable
               then
                  Pattern.Discrs := Var.Discrs;
                  Get_Item_From_Expr
                    (Pattern     => Pattern,
                     Expr        => Expr,
                     Context     => Context,
                     Args        => Args,
                     Constr_Expr => Constr_Expr,
                     Reuse_Discr => True,
                     Need_Store  => Need_Store);
                  return;
               else
                  Get_Item_From_Expr
                    (Pattern     => Pattern,
                     Expr        => Expr,
                     Context     => Context,
                     Args        => Args,
                     Constr_Expr => Constr_Expr,
                     Need_Store  => Need_Store);
                  return;
               end if;
            end if;

            --  Try to reuse the Discrs identifier from Var

            if Pattern.Discrs.Present then
               pragma Assert (Var.Discrs.Present);

               --  If both are similarly mutable, we can reuse the discriminant
               --  identifier as all convertible record types share the
               --  same discriminants.

               if Var.Discrs.Binder.Mutable = Pattern.Discrs.Binder.Mutable
               then
                  Pattern.Discrs := Var.Discrs;
                  Args (Count) := +Var.Discrs.Binder.B_Name;

               --  If the formal has mutable discriminants and not the actual,
               --  we need to create a new reference.

               elsif Pattern.Discrs.Binder.Mutable then
                  Context.Append
                    (Ref_Type'(Mutable => True,
                               Name    => Pattern.Discrs.Binder.B_Name,
                               Value   => +Var.Discrs.Binder.B_Name));
                  Need_Store := True;
                  Args (Count) := +Pattern.Discrs.Binder.B_Name;

               --  If the actual has mutable discriminants and not the formal,
               --  we need a dereference.

               else
                  Args (Count) := New_Deref
                    (Right => Var.Discrs.Binder.B_Name,
                     Typ   => Get_Typ (Var.Discrs.Binder.B_Name));
               end if;
               Count := Count + 1;
            end if;

            --  Take the Constr field of Var if present

            if Pattern.Constr.Present and Var.Constr.Present then
               Args (Count) := +Var.Constr.Id;

               Count := Count + 1;

            --  Otherwise, use Constr_Expr

            elsif Pattern.Constr.Present then
               Args (Count) := Constr_Expr;

               Count := Count + 1;
            end if;

            if Pattern.Tag.Present then
               pragma Assert (Var.Tag.Present);
               Args (Count) := +Var.Tag.Id;

               Count := Count + 1;
            end if;

         when UCArray =>

            --  We can reuse the content of Var if no sliding might occur as
            --  part of the conversion between Pattern and Var.

            if Eq_Base (Get_Why_Type_From_Item (Pattern),
                        Get_Why_Type_From_Item (Var))
              or else not Needs_Slide (Get_Ada_Type_From_Item (Pattern),
                                       Get_Ada_Type_From_Item (Var))
            then

               --  The actual can be either an array in split form or a
               --  statically constrained array.
               --  If the actual is a split array, use elements from its
               --  binder.

               if Var.Kind = UCArray then
                  Args (Count) := +Var.Content.B_Name;
                  Count := Count + 1;

                  for Dim_Index in 1 .. Var.Dim loop
                     Args (Count) := +Var.Bounds (Dim_Index).First;
                     Args (Count + 1) := +Var.Bounds (Dim_Index).Last;
                     Count := Count + 2;
                  end loop;

               --  Otherwise, the actual is a static constrained array.
               --  We can reuse its identifier for the content but we must
               --  use its type to get the bounds.

               else
                  pragma Assert
                    (Var.Kind = Regular and then Var.Main.Mutable
                     and then Is_Static_Array_Type
                       (Get_Ada_Type_From_Item (Var)));

                  Args (Count) := +Var.Main.B_Name;
                  Count := Count + 1;

                  declare
                     Arr_Ty : constant Entity_Id :=
                       Get_Ada_Type_From_Item (Var);
                  begin
                     for Dim_Index in 1 .. Pattern.Dim loop
                        Args (Count) :=
                          Insert_Simple_Conversion
                            (Domain   => EW_Prog,
                             Expr     => Get_Array_Attr
                               (Domain => EW_Prog,
                                Ty     => Arr_Ty,
                                Attr   => Attribute_First,
                                Dim    => Dim_Index),
                             To       =>
                               Get_Typ (Pattern.Bounds (Dim_Index).First));
                        Args (Count + 1) :=
                          Insert_Simple_Conversion
                            (Domain   => EW_Prog,
                             Expr     => Get_Array_Attr
                               (Domain => EW_Prog,
                                Ty     => Arr_Ty,
                                Attr   => Attribute_Last,
                                Dim    => Dim_Index),
                             To       =>
                               Get_Typ (Pattern.Bounds (Dim_Index).Last));
                        Count := Count + 2;
                     end loop;
                  end;
               end if;

            --  Otherwise, the identifiers of the actual cannot be used.
            --  Use the expression instead.

            else
               Get_Item_From_Expr
                 (Pattern     => Pattern,
                  Expr        => Expr,
                  Constr_Expr => Constr_Expr,
                  Context     => Context,
                  Args        => Args,
                  Need_Store  => Need_Store);
               return;
            end if;

         when Pointer =>

            --  We can always reuse the reference for the value of split
            --  pointers, since pointers designating the same type share a
            --  single Why type.

            pragma Assert (Var.Kind = Pointer);
            Args (Count) := +Var.Value.B_Name;
            Count := Count + 1;

            if Pattern.Mutable = Var.Mutable then
               Args (Count) := +Var.Address;
               Count := Count + 1;
               Args (Count) := +Var.Is_Null;
               Count := Count + 1;
            else
               pragma Assert (not Pattern.Mutable);
               Args (Count) := New_Deref
                 (Right => Var.Address,
                  Typ   => Get_Typ (Var.Address));
               Count := Count + 1;
               Args (Count) := New_Deref
                 (Right => Var.Is_Null,
                  Typ   => Get_Typ (Var.Is_Null));
               Count := Count + 1;
            end if;

            Args (Count) := +Var.Is_Moved;
            Count := Count + 1;

         when Func    =>
            raise Program_Error;
      end case;
   end Get_Item_From_Var;

   -------------------------------------
   -- Get_Pure_Logic_Term_If_Possible --
   -------------------------------------

   function Get_Pure_Logic_Term_If_Possible
     (File          : W_Section_Id;
      Expr          : Node_Id;
      Expected_Type : W_Type_Id) return W_Term_Id
   is
      Params : constant Transformation_Params :=
        (File        => File,
         Phase       => Generate_Logic,
         Gen_Marker  => GM_None,
         Ref_Allowed => True,
         Old_Policy  => As_Old);
      Result : constant W_Term_Id :=
        +Transform_Expr (Expr, Expected_Type, EW_Term, Params);
   begin
      if Has_Dereference_Or_Any_Or_Self (Result) then
         return Why_Empty;
      else
         return Result;
      end if;
   end Get_Pure_Logic_Term_If_Possible;

   -------------------------------
   -- Has_Visibility_On_Refined --
   -------------------------------

   function Has_Visibility_On_Refined
     (Expr : Node_Id;
      E    : Entity_Id)
      return Boolean
   is
    (Subprogram_Refinement_Is_Visible (E, Get_Flow_Scope (Expr)));

   -------------------------------
   -- Havoc_Borrowed_Expression --
   -------------------------------

   function Havoc_Borrowed_Expression (Brower : Entity_Id) return W_Prog_Id
   is
      Borrowed    : constant Entity_Id := Get_Borrowed_Entity (Brower);
      Expr        : constant Node_Id := Get_Borrowed_Expr (Brower);
      Ty          : constant Entity_Id := Get_Borrowed_Typ (Brower);
      Borrowed_Id : constant W_Identifier_Id :=
        New_Temp_Identifier
          (Base_Name => "borrowed", Typ => Type_Of_Node (Borrowed));
      Expr_Id     : constant W_Identifier_Id :=
        New_Temp_Identifier
          (Base_Name => "borrowed_expr", Typ => Type_Of_Node (Ty));
      W_Expr      : W_Expr_Id;
      Havoc_Expr  : W_Prog_Id;

   begin
      --  If the borrowed object is not mutable (it happens when we are inside
      --  a traversal function), nothing needs to be done.

      if not Is_Mutable_In_Why (Borrowed) then
         return +Void;
      end if;

      --  Store in W_Expr the expression tmp_borrowed.Expr. We convert it to
      --  Ty because it may not respect the constraints of the type of
      --  Borrowed.Expr, so we will need to convert it back later with checks
      --  enabled.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      Insert_Entity (Borrowed, Borrowed_Id);
      W_Expr := Insert_Simple_Conversion
           (Domain => EW_Pterm,
            Expr   => Transform_Expr
              (Expr    => Expr,
               Domain  => EW_Pterm,
               Params  => Body_Params),
            To     => Type_Of_Node (Ty));
      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      --  We produce:
      --
      --  let tmp_borrowed = any <Etype (Borrowed)> in
      --  let tmp_borrowed_expr = (to_ty tmp_borrowed.Expr) in
      --  assume { dyn_prop tmp_borrowed_expr
      --            /\ pledge tmp_borrowed Brower
      --            /\ assumption_for_borrow };
      --  borrowed.Expr := tmp_borrowed_expr
      --
      --  Note that we cannot assume the dynamic invariant of tmp_borrowed,
      --  we check it later when assigning to borrowed.Expr. We assume the
      --  dynamic property of tmp_borrowed_expr however as its preservation
      --  is enforced by language restrictions (we do not allow borrowing
      --  types with predicates on deep parts).

      Havoc_Expr := Sequence
        ((1 => New_Assume_Statement
          (Pred => +New_And_Expr
           (Domain    => EW_Pred,
            Conjuncts =>
              (1 => +Compute_Dynamic_Invariant
                 (Expr        => +Expr_Id,
                  Ty          => Ty,
                  Params      => Body_Params,
                  Initialized => True_Term),
               2 => +Pred_Of_Boolean_Term
                 (+New_Pledge_Call
                      (E            => Brower,
                       Borrowed_Arg => +Borrowed_Id,
                       Brower_Arg   => Transform_Identifier
                         (Params   => Body_Params,
                          Expr     => Brower,
                          Ent      => Brower,
                          Domain   => EW_Term),
                       Ref_Allowed => True)),
               3 => +Compute_Assumption_For_Borrow
                 (Brower,
                  Borrowed_Id,
                  Body_Params)))),
          2 => New_Assignment
            (Lvalue => Expr,
             Expr   => +Insert_Checked_Conversion
               (Ada_Node => Brower,
                Domain   => EW_Prog,
                Expr     => +Expr_Id,
                To       => Type_Of_Node (Etype (Expr)),
                Lvalue   => True))));

      return
        New_Binding
          (Name    => Borrowed_Id,
           Def     => New_Any_Expr
             (Return_Type => Type_Of_Node (Borrowed),
              Labels      => Symbol_Sets.Empty_Set),
           Context =>
             New_Binding
               (Domain  => EW_Prog,
                Name    => Expr_Id,
                Def     => W_Expr,
                Context => +Havoc_Expr));
   end Havoc_Borrowed_Expression;

   -------------------------------
   -- Havoc_Borrowed_From_Block --
   -------------------------------

   function Havoc_Borrowed_From_Block
     (N : Node_Id) return W_Statement_Sequence_Id
   is
   begin
      return Result  : W_Statement_Sequence_Id := Void_Sequence do
         if Present (Declarations (N)) then
            declare
               Borrows : Node_Lists.List;
            begin
               Get_Borrows_From_Decls (Declarations (N), Borrows);
               for E of Borrows loop
                  Sequence_Append
                    (Result,
                     Havoc_Borrowed_Expression (E));
               end loop;
            end;
         end if;
      end return;
   end Havoc_Borrowed_From_Block;

   ----------------------------
   -- Insert_Invariant_Check --
   ----------------------------

   function Insert_Invariant_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      W_Expr   : W_Prog_Id;
      Var_Ent  : Entity_Id := Empty) return W_Prog_Id
   is
      W_Tmp : constant W_Identifier_Id :=
        New_Temp_Identifier (Typ      => Get_Type (+W_Expr),
                             Ada_Node => Var_Ent);
      --  If W_Expr is an array in split form, we need to link W_Tmp to Var_Ent
      --  so that the proper bounds can be retrieved.

      W_Seq : constant W_Prog_Id :=
        Sequence (New_Invariant_Check (Ada_Node, Check_Ty, +W_Tmp), +W_Tmp);
   begin
      return +W_Expr_Id'(New_Binding (Ada_Node => Ada_Node,
                                      Domain   => EW_Prog,
                                      Name     => W_Tmp,
                                      Def      => +W_Expr,
                                      Context  => +W_Seq,
                                      Typ      => Get_Type (+W_Expr)));
   end Insert_Invariant_Check;

   -------------------------------
   -- Insert_Move_Of_Deep_Parts --
   -------------------------------

   procedure Insert_Move_Of_Deep_Parts
     (Stmt    : Node_Id;
      Lhs_Typ : Entity_Id;
      Expr    : in out W_Prog_Id)
   is
      --  Local subprograms

      function Can_Be_Moved (Expr : Node_Id) return Boolean;
      --  Return whether an expression can be moved

      procedure Collect_Moved_Objects
        (Expr     : Node_Id;
         Toplevel : Boolean;
         Map      : in out Ada_To_Why_Ident.Map);
      --  Add in Map all moved objects from Expr. If Toplevel is True, this is
      --  the outter toplevel call, for which the top-level object should not
      --  be inserted in the map as it is handled specially.

      ------------------
      -- Can_Be_Moved --
      ------------------

      function Can_Be_Moved (Expr : Node_Id) return Boolean is
         Typ : constant Entity_Id := Retysp (Etype (Expr));
      begin
         return Is_Deep (Typ)
          and then not Is_Anonymous_Access_Type (Typ)
          and then Present (Get_Root_Object (Expr));
      end Can_Be_Moved;

      ---------------------------
      -- Collect_Moved_Objects --
      ---------------------------

      procedure Collect_Moved_Objects
        (Expr     : Node_Id;
         Toplevel : Boolean;
         Map      : in out Ada_To_Why_Ident.Map)
      is
      begin
         --  Object can be moved, insert it in the map unless at top-level

         if not Toplevel
           and then Can_Be_Moved (Expr)
         then
            Map.Insert
              (Expr,
               New_Temp_Identifier (Typ => Type_Of_Node (Expr)));
            return;
         end if;

         --  Otherwise, look at sub-objects that may be moved

         case Nkind (Expr) is
            when N_Qualified_Expression
               | N_Type_Conversion
               | N_Unchecked_Type_Conversion
            =>
               Collect_Moved_Objects
                 (Expression (Expr), Toplevel => Toplevel, Map => Map);

            --  No move occurs in an uninitialized allocator

            when N_Allocator =>
               if Nkind (Expression (Expr)) = N_Qualified_Expression then
                  Collect_Moved_Objects
                    (Expression (Expr), Toplevel => False, Map => Map);
               end if;

            when N_Aggregate =>
               declare
                  Exprs  : constant List_Id := Expressions (Expr);
                  Assocs : constant List_Id := Component_Associations (Expr);

                  Expression  : Node_Id;
                  Association : Node_Id;
               begin
                  Expression :=
                    (if Nlists.Is_Empty_List (Exprs) then Empty
                     else Nlists.First (Exprs));
                  while Present (Expression) loop
                     Collect_Moved_Objects
                       (Expression,
                        Toplevel => False,
                        Map      => Map);
                     Next (Expression);
                  end loop;

                  Association :=
                    (if Nlists.Is_Empty_List (Assocs) then Empty
                     else Nlists.First (Assocs));
                  while Present (Association) loop
                     if Present (SPARK_Atree.Expression (Association)) then
                        Collect_Moved_Objects
                          (SPARK_Atree.Expression (Association),
                           Toplevel => False,
                           Map      => Map);
                     end if;
                     Next (Association);
                  end loop;
               end;

            when others =>
               null;
         end case;
      end Collect_Moved_Objects;

      --  Local variables

      Rhs           : constant Node_Id := Expression (Stmt);
      Toplevel_Move : constant Boolean := Can_Be_Moved (Rhs);
      Nested_Moved  : Ada_To_Why_Ident.Map;
      Do_Move       : Boolean;
      Tmp           : W_Identifier_Id;
      Init          : W_Prog_Id;

   --  Start of processing for Insert_Move_Of_Deep_Parts

   begin
      --  There is no move at all for a borrow or observe

      if Is_Anonymous_Access_Type (Lhs_Typ) then
         Do_Move := False;

      --  Collect all deep objects potentially moved inside an aggregate

      else
         Collect_Moved_Objects (Rhs, Toplevel => True, Map => Nested_Moved);
         Do_Move := Toplevel_Move or else not Nested_Moved.Is_Empty;
      end if;

      if Do_Move then
         Tmp  := New_Temp_Identifier (Typ => Get_Type (+Expr));
         Init := Expr;
         Expr := +Tmp;
      end if;

      if Do_Move then
         for Mapping in Nested_Moved.Iterate loop
            declare
               Obj     : Node_Id renames Ada_To_Why_Ident.Key (Mapping);
               Obj_Tmp : W_Identifier_Id renames Nested_Moved (Mapping);
            begin
               Expr := New_Binding
                 (Name    => Obj_Tmp,
                  Def     => Transform_Expr (Obj, EW_Term, Body_Params),
                  Context => +Sequence (Move_Expression (Obj, Obj_Tmp), +Expr),
                  Typ     => Get_Type (+Expr));
            end;
         end loop;

         Expr := New_Binding
           (Name    => Tmp,
            Def     => +Init,
            Context =>
              (if Toplevel_Move then
                 +Sequence (Move_Expression (Rhs, Tmp), +Expr)
               else +Expr),
            Typ     => Get_Type (+Expr));
      end if;
   end Insert_Move_Of_Deep_Parts;

   ---------------------------
   -- Insert_Overflow_Check --
   ---------------------------

   function Insert_Overflow_Check
     (Ada_Node : Node_Id;
      T        : W_Expr_Id;
      In_Type  : Entity_Id;
      Is_Float : Boolean) return W_Expr_Id
   is
      Base : constant Entity_Id := Base_Type (In_Type);

   begin
      return New_VC_Call (Domain   => EW_Prog,
                          Ada_Node => Ada_Node,
                          Name     => E_Symb (Base, WNE_Range_Check_Fun),
                          Progs    => (1 => +T),
                          Reason   =>
                            (if Is_Float then VC_FP_Overflow_Check
                             else VC_Overflow_Check),
                          Typ      => Get_Type (T));
   end Insert_Overflow_Check;

   ----------------------------
   -- Insert_Predicate_Check --
   ----------------------------

   function Insert_Predicate_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      W_Expr   : W_Prog_Id;
      Var_Ent  : Entity_Id := Empty) return W_Prog_Id
   is
      Init_Expr : constant W_Expr_Id :=
        (if Is_Init_Wrapper_Type (Get_Type (+W_Expr))
         and then not Has_Relaxed_Init (Check_Ty)
         then Insert_Initialization_Check
           (Ada_Node               => Ada_Node,
            E                      => Get_Ada_Node (+Get_Type (+W_Expr)),
            Name                   => +W_Expr,
            Domain                 => EW_Prog,
            Exclude_Always_Relaxed => True)
         else +W_Expr);
      --  If Check_Ty does not itself have relaxed init, then its predicate
      --  expects an initialized expression.

      W_Tmp     : constant W_Identifier_Id :=
        New_Temp_Identifier (Typ      => Get_Type (Init_Expr),
                             Ada_Node => Var_Ent);
      --  If W_Expr is an array in split form, we need to link W_Tmp to Var_Ent
      --  so that the proper bounds can be retrieved.

      W_Seq : constant W_Prog_Id :=
        Sequence (New_Predicate_Check (Ada_Node, Check_Ty, +W_Tmp), +W_Tmp);
   begin
      return +W_Expr_Id'(New_Binding (Ada_Node => Ada_Node,
                                      Domain   => EW_Prog,
                                      Name     => W_Tmp,
                                      Def      => Init_Expr,
                                      Context  => +W_Seq,
                                      Typ      => Get_Type (Init_Expr)));
   end Insert_Predicate_Check;

   ------------------------
   -- Insert_Ref_Context --
   ------------------------

   function Insert_Ref_Context
     (Ada_Call : Node_Id;
      Why_Call : W_Prog_Id;
      Context  : Ref_Context;
      Store    : W_Statement_Sequence_Unchecked_Id) return W_Prog_Id
   is
      Ref_Context : W_Prog_Id;
      Subp        : constant Entity_Id := Get_Called_Entity (Ada_Call);

   begin
      --  In the case of a procedure or entry call, there is no value to return
      --  as the final expression, so just prepend the call at the start of the
      --  sequence.

      if Nkind (Ada_Call) in N_Procedure_Call_Statement
                           | N_Entry_Call_Statement
      then
         Statement_Sequence_Prepend_To_Statements (Store, Why_Call);

         --  We need to havoc the values of global variables of mode Output if
         --  they have parts with relaxed initialization so that their value
         --  before the call cannot leak into subsequently read values.

         declare
            Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
            Write_Ids : Flow_Types.Flow_Id_Sets.Set;
            Effects   : constant W_Effects_Id := New_Effects;

         begin
            Flow_Utility.Get_Proof_Globals (Subprogram      => Subp,
                                            Reads           => Read_Ids,
                                            Writes          => Write_Ids,
                                            Erase_Constants => True);

            for Write_Id of Write_Ids loop
               if not Read_Ids.Contains (Write_Id) then
                  case Write_Id.Kind is
                     when Direct_Mapping =>
                        declare
                           Entity : constant Entity_Id :=
                             Get_Direct_Mapping_Id (Write_Id);
                           Binder : constant Item_Type :=
                             Ada_Ent_To_Why.Element (Symbol_Table, Entity);

                        begin
                           if Contains_Relaxed_Init_Parts (Etype (Entity))
                             or else Obj_Has_Relaxed_Init (Entity)
                           then
                              case Binder.Kind is
                                 when DRecord =>
                                    pragma Assert (Binder.Fields.Present);
                                    Effects_Append_To_Writes
                                      (Effects, Binder.Fields.Binder.B_Name);
                                 when UCArray =>
                                    Effects_Append_To_Writes
                                      (Effects, Binder.Content.B_Name);
                                 when Regular =>
                                    Effects_Append_To_Writes
                                      (Effects, Binder.Main.B_Name);
                                 when others => raise Program_Error;
                              end case;

                              if Binder.Init.Present then
                                 Effects_Append_To_Writes
                                   (Effects, Binder.Init.Id);
                              end if;
                           end if;
                        end;
                     when Magic_String =>
                        Effects_Append_To_Writes
                          (Effects,
                           To_Why_Id (Obj   => To_Name (Write_Id),
                                      Local => False));
                     when others =>
                        raise Program_Error;
                  end case;
               end if;
            end loop;
            Statement_Sequence_Prepend_To_Statements
                (Store,
                 New_Havoc_Statement
                   (Ada_Node => Ada_Call,
                    Effects  => Effects));
         end;
      end if;

      --  Set the pieces together

      Ref_Context := +Store;

      --  In the case of a function call, there is value to return as the
      --  final expression. Note that this can only occur for calls to volatile
      --  functions, when one of the parameters is of a volatile type. Save the
      --  result of the call at the start of the sequence (Ref_Context consists
      --  in the sequence of post-call assignments and assumptions at this
      --  point) and use it as the final value for the sequence.

      if Nkind (Ada_Call) = N_Function_Call then
         declare
            Tmp : constant W_Identifier_Id :=
              New_Temp_Identifier (Ada_Call, Get_Type (+Why_Call));
         begin
            Ref_Context :=
              +New_Typed_Binding (Domain  => EW_Prog,
                                  Name    => Tmp,
                                  Def     => +Why_Call,
                                  Context =>
                                    +Sequence (Ref_Context, +Tmp));
         end;
      end if;

      for J of reverse Context loop
         if J.Mutable then
            Ref_Context :=
              New_Binding_Ref
                (Name    => J.Name,
                 Def     => +J.Value,
                 Context => Ref_Context,
                 Typ     => Get_Type (+Ref_Context));
         else
            Ref_Context :=
              +New_Typed_Binding
              (Domain   => EW_Prog,
               Name     => J.Name,
               Def      => J.Value,
               Context  => +Ref_Context);
         end if;
      end loop;

      return Ref_Context;
   end Insert_Ref_Context;

   ----------------------
   -- Is_Simple_Actual --
   ----------------------

   function Is_Simple_Actual (Actual : Node_Id) return Boolean is
   begin
      return
        Nkind (Actual) in N_Identifier | N_Expanded_Name
          and then
        not Is_Protected_Component_Or_Discr_Or_Part_Of (Entity (Actual));
   end Is_Simple_Actual;

   ----------------------
   -- Is_Terminal_Node --
   ----------------------

   function Is_Terminal_Node (N : Node_Id) return Boolean is
   begin
      return Nkind (N) not in N_Quantified_Expression |
                              N_And_Then              |
                              N_Op_And                |
                              N_If_Expression;
   end Is_Terminal_Node;

   ------------------------
   -- Map_For_Loop_Entry --
   ------------------------

   function Map_For_Loop_Entry
     (Loop_Id : Node_Id) return Ada_To_Why_Ident.Map
   is
      use Loop_Entry_Nodes;
      C : constant Loop_Entry_Nodes.Cursor := Loop_Entry_Map.Find (Loop_Id);
   begin
      return (if Has_Element (C) then
                 Element (C)
              else
                 Ada_To_Why_Ident.Empty_Map);
   end Map_For_Loop_Entry;

   ---------------------
   -- Move_Expression --
   ---------------------

   function Move_Expression
     (Expr : Node_Id;
      Tmp  : W_Identifier_Id) return W_Prog_Id
   is
      Typ         : constant Entity_Id := Retysp (Etype (Expr));

   begin
      --  Reach out past a type conversion or qualification

      if Nkind (Expr) in N_Qualified_Expression
                       | N_Type_Conversion
                       | N_Unchecked_Type_Conversion
      then
         return Move_Expression (Expression (Expr), Tmp);

      --  For a pointer, we update the is_moved field to true.

      elsif Is_Access_Type (Typ) then

         --  For whole objects, we simply assign the is_moved field.
         --
         --  is_moved := true

         if Is_Simple_Actual (Expr) then
            declare
               Binder : constant Item_Type :=
                 Ada_Ent_To_Why.Element (Symbol_Table, Entity (Expr));
            begin
               pragma Assert (Binder.Kind = Pointer);

               return New_Assignment
                    (Name   => Binder.Is_Moved,
                     Value  => True_Prog,
                     Typ    => EW_Bool_Type,
                     Labels => Symbol_Sets.Empty_Set);
            end;

         --  Reconstruct the new pointer value before storing it in Expr
         --
         --  expr := { expr with is_moved => true }

         else
            return Gnat2Why.Expr.New_Assignment
              (Lvalue   => Expr,
               Expr     => +New_Pointer_Is_Moved_Update
                 (E      => Typ,
                  Name   => +Tmp,
                  Value  => +True_Prog,
                  Domain => EW_Prog),
               No_Check => True);
         end if;

      --  We need to call the __move function on Tmp

      else
         declare
            Pattern    : Item_Type := Move_Param_Item (Typ);
            Need_Store : Boolean;
            Context    : Ref_Context;
            Args       : W_Expr_Array
              (1 .. Item_Array_Length ((1 => Pattern)));
            T          : W_Prog_Id;

         begin
            --  If Expr is a whole object, try to reuse the references of Expr

            if Is_Simple_Actual (Expr) then
               declare
                  Binder : constant Item_Type :=
                    Ada_Ent_To_Why.Element (Symbol_Table, Entity (Expr));
               begin
                  pragma Assert (Binder.Kind in UCArray | DRecord | Regular);

                  Get_Item_From_Var
                    (Pattern     => Pattern,
                     Var         => Binder,
                     Expr        => +Tmp,
                     Context     => Context,
                     Args        => Args,
                     Constr_Expr => Why_Empty,
                     Need_Store  => Need_Store);
               end;

            --  Otherwise, compute new references from Tmp directly

            else
               Get_Item_From_Expr
                 (Pattern     => Pattern,
                  Expr        => +Tmp,
                  Context     => Context,
                  Args        => Args,
                  Constr_Expr => Why_Empty,
                  Need_Store  => Need_Store);
            end if;

            --  Call the appropriate __move function

            T := New_Call
              (Name => E_Symb (Typ, WNE_Move),
               Args => Args,
               Typ  => EW_Unit_Type);

            --  If needed store back values inside Expr

            if Need_Store then
               declare
                  Reconstructed_Tmp : constant W_Prog_Id :=
                    Reconstruct_Expr_From_Item
                      (Pattern    => Pattern,
                       Actual     => Expr,
                       No_Checks  => True,
                       Pre_Expr   => +Tmp);
               begin
                  T := Sequence
                    (T,
                     Gnat2Why.Expr.New_Assignment
                       (Lvalue   => Expr,
                        Expr     => Reconstructed_Tmp,
                        No_Check => True));
               end;
            end if;

            --  And possibly declare new references

            for J of reverse Context loop
               if J.Mutable then
                  T :=
                    New_Binding_Ref
                      (Name    => J.Name,
                       Def     => +J.Value,
                       Context => T,
                       Typ     => EW_Unit_Type);
               else
                  T :=
                    +New_Typed_Binding
                    (Domain   => EW_Prog,
                     Name     => J.Name,
                     Def      => J.Value,
                     Context  => +T);
               end if;
            end loop;

            return T;
         end;
      end if;
   end Move_Expression;

   -------------------------
   -- Name_For_Loop_Entry --
   -------------------------

   function Name_For_Loop_Entry
     (Expr    : Node_Id;
      Loop_Id : Node_Id) return W_Identifier_Id
   is
      Result : W_Identifier_Id;

      procedure Get_Name
        (Loop_Id  : Node_Id;
         Loop_Map : in out Ada_To_Why_Ident.Map);
      --  Update the mapping Loop_Map with an entry for Expr if not already
      --  present, and store the corresponding identifier in Result.

      --------------
      -- Get_Name --
      --------------

      procedure Get_Name
        (Loop_Id  : Node_Id;
         Loop_Map : in out Ada_To_Why_Ident.Map)
      is
         Typ : W_Type_Id;
         Nd  : Node_Id;

         Pos   : Ada_To_Why_Ident.Cursor := Loop_Map.Find (Expr);
         Dummy : Boolean;

         use Ada_To_Why_Ident;

         Attrs : Common_Containers.String_Sets.Set :=
                   Common_Containers.String_Sets.Empty_Set;
         Model_Trace : constant String :=
           --  Here we exclude Loop_Entry expressions and only consider
           --  Entities
           (if Nkind (Expr) in N_Has_Entity then
               "model_trace:" &
               Trim (Source => Entity (Expr)'Image,
                     Side   => Ada.Strings.Left) &
              "'Loop_Entry"
            else "");

      begin
         pragma Unreferenced (Loop_Id);

         if not Has_Element (Pos) then

            if Nkind (Expr) in N_Defining_Identifier then
               Typ := Why_Type_Of_Entity (Expr);
               Nd  := Expr;
            elsif Nkind (Expr) in N_Identifier | N_Expanded_Name then
               Typ := Why_Type_Of_Entity (Entity (Expr));
               Nd  := Entity (Expr);
            else
               Typ := Type_Of_Node (Expr);
               Nd  := Empty;
            end if;

            if Model_Trace /= "" then
               Common_Containers.String_Sets.Insert (Attrs, Model_Trace);
            end if;
            Loop_Map.Insert (Key      => Expr,
                             New_Item => New_Generated_Identifier
                                           (Typ       => Typ,
                                            Ada_Node  => Nd,
                                            Base_Name => "loop_entry",
                                            Attrs     => Attrs),
                             Position => Pos,
                             Inserted => Dummy);
         end if;

         Result := Loop_Map (Pos);
      end Get_Name;

      Cur   : Loop_Entry_Nodes.Cursor;
      Dummy : Boolean;

   --  Start of processing for Name_For_Loop_Entry

   begin
      Loop_Entry_Map.Insert
        (Key      => Loop_Id,
         Position => Cur,
         Inserted => Dummy);

      Loop_Entry_Map.Update_Element
        (Position => Cur,
         Process  => Get_Name'Access);

      return Result;
   end Name_For_Loop_Entry;

   ------------------
   -- Name_For_Old --
   ------------------

   function Name_For_Old (N : Node_Id) return W_Identifier_Id is
      Position : Ada_To_Why_Ident.Cursor;
      Inserted : Boolean;

      use Ada_To_Why_Ident;

   begin
      --  Tentatively insert an empty node to update it later
      Old_Map.Insert (Key      => N,
                      New_Item => Why_Empty,
                      Position => Position,
                      Inserted => Inserted);

      if Inserted then
         declare
            function Is_Contract_Case (P : Node_Id) return Boolean is
              (Is_Pragma (P, Pragma_Contract_Cases));

            function Enclosing_Contract_Case is new
              First_Parent_With_Property (Is_Contract_Case);

            Typ : W_Type_Id;
            Nd  : Node_Id;
            Attrs : Common_Containers.String_Sets.Set :=
                   Common_Containers.String_Sets.Empty_Set;
            Model_Trace : constant String :=
              --  Here we exclude Old expressions and only consider Entities
              (if Nkind (N) in N_Has_Entity then
                  "model_trace:" &
                  Trim (Source => Entity (N)'Image,
                        Side   => Ada.Strings.Left) &
                 "'Old"
               else "");
         begin
            if Nkind (N) in N_Identifier | N_Expanded_Name then
               Typ := Type_Of_Node (N);
               Nd  := Entity (N);
            else
               Typ := Type_Of_Node (Etype (N));
               Nd  := Empty;
            end if;

            if Present (Enclosing_Contract_Case (N)) and then
              Model_Trace /= ""
            then
               Common_Containers.String_Sets.Insert (Attrs, Model_Trace);
               Old_Map (Position) :=
                 New_Generated_Identifier
                   (Base_Name => "old",
                    Typ       => Typ,
                    Ada_Node  => Nd,
                    Attrs     => Attrs);
            else
               Old_Map (Position) :=
                 New_Temp_Identifier (Base_Name => "old",
                                      Typ       => Typ,
                                      Ada_Node  => Nd);
            end if;
         end;
      end if;

      return Old_Map (Position);
   end Name_For_Old;

   --------------------
   -- New_Assignment --
   --------------------

   function New_Assignment
     (Ada_Node : Node_Id := Empty;
      Lvalue   : Node_Id;
      Expr     : W_Prog_Id;
      No_Check : Boolean := False) return W_Prog_Id
   is
      --  Here, we deal with assignment statements. In SPARK, the general form
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

      Left_Side   : Node_Id   := Lvalue;
      Right_Side  : W_Expr_Id := +Expr;
      Last_Access : Node_Id   := Empty;
      Result      : W_Prog_Id := +Void;
      Domain      : constant EW_Domain :=
        (if No_Check then EW_Pterm else EW_Prog);

   --  Start of processing for New_Assignment

   begin
      --  When assigning to the view conversion of an object, it is really the
      --  object which will be assigned to in Why3. So start with skipping all
      --  view conversions, so that the correct type of object is used later.

      while Nkind (Left_Side) in N_Type_Conversion
                               | N_Unchecked_Type_Conversion
      loop
         Shift_Rvalue (Left_Side, Right_Side, Last_Access, Domain);
      end loop;

      --  Record attributes of objects are not modified by assignments

      declare
         Ty : constant Entity_Id := Etype (Left_Side);
      begin
         if Is_Record_Type_In_Why (Ty) then
            Right_Side :=
              +New_Tag_Update
              (Ada_Node  => Ada_Node,
               Domain    => Domain,
               Name      => +Right_Side,
               From_Expr => Transform_Expr (Left_Side, EW_Pterm, Body_Params),
               Ty        => Ty);
         end if;
      end;

      while not (Nkind (Left_Side) in N_Identifier | N_Expanded_Name) loop
         Shift_Rvalue (Left_Side, Right_Side, Last_Access, Domain);
      end loop;

      --  In those cases where the left-hand side is type converted, the type
      --  of the Left_Side and Right_Side may not coincide here. Convert the
      --  Right_Side to the type of the Left_Side. Possible checks were taken
      --  into account before.

      Right_Side :=
        +Insert_Simple_Conversion (Domain => EW_Pterm,
                                   To     => Type_Of_Node (Left_Side),
                                   Expr   => +Right_Side);

      --  In the case of protected components, we have to generate the record
      --  code ourselves on top.

      if Is_Protected_Component_Or_Discr_Or_Part_Of (Entity (Left_Side)) then
         declare
            Prot_Obj : constant W_Identifier_Id := Self_Name;

         begin
            pragma Assert (Self_Is_Mutable);

            Result :=
              New_Assignment
                (Ada_Node => Ada_Node,
                 Name     => Prot_Obj,
                 Labels   => Symbol_Sets.Empty_Set,
                 Value    =>
                   +One_Level_Update
                     (Left_Side,
                      New_Deref (Right => +Prot_Obj,
                                 Typ   => Get_Typ (Prot_Obj)),
                      +Right_Side,
                      Domain,
                      Body_Params),
                 Typ     => Get_Typ (Prot_Obj));
         end;
      else
         declare
            Binder : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, Entity (Left_Side));
         begin
            --  Assign initialization flag if any

            if Binder.Init.Present then
               Result :=
                 New_Assignment
                   (Ada_Node => Ada_Node,
                    Name     => Binder.Init.Id,
                    Labels   => Symbol_Sets.Empty_Set,
                    Value    => True_Prog,
                    Typ      => EW_Bool_Type);
            end if;

            case Binder.Kind is
            when Regular =>
               Result := Sequence
                 (Result,
                  New_Assignment
                    (Ada_Node => Ada_Node,
                     Name     => Binder.Main.B_Name,
                     Labels   => Symbol_Sets.Empty_Set,
                     Value    => +Right_Side,
                     Typ      => Get_Typ (Binder.Main.B_Name)));

            when UCArray =>
               Result := Sequence
                 (Result,
                  New_Assignment
                    (Ada_Node => Ada_Node,
                     Name     => Binder.Content.B_Name,
                     Labels   => Symbol_Sets.Empty_Set,
                     Value    => +Right_Side,
                     Typ      => Get_Typ (Binder.Content.B_Name)));

            when DRecord =>
               declare
                  Tmp : constant W_Expr_Id := New_Temp_For_Expr (+Right_Side);

               begin
                  pragma Assert
                    (No (Last_Access)
                     or else (Nkind (Last_Access) = N_Selected_Component
                       and then Ekind (Entity (Selector_Name (Last_Access))) /=
                         E_Discriminant));

                  if Binder.Fields.Present then
                     Result := Sequence
                       (Result, New_Assignment
                          (Ada_Node => Ada_Node,
                           Name     => Binder.Fields.Binder.B_Name,
                           Labels   => Symbol_Sets.Empty_Set,
                           Value    => +New_Fields_Access
                             (Domain   => Domain,
                              Name     => Tmp,
                              Ty       => Binder.Typ),
                           Typ      => Get_Typ (Binder.Fields.Binder.B_Name)));
                  end if;

                  --  Discriminants cannot have been updated if the last access
                  --  was a selected components as discriminants can only be
                  --  modified when the object is assigned as a whole.

                  if Binder.Discrs.Present and then No (Last_Access) then
                     if Binder.Discrs.Binder.Mutable then
                        Result := Sequence
                          (Result, New_Assignment
                             (Ada_Node => Ada_Node,
                              Name     => Binder.Discrs.Binder.B_Name,
                              Labels   => Symbol_Sets.Empty_Set,
                              Value    => +New_Discriminants_Access
                                (Domain => Domain,
                                 Name   => Tmp,
                                 Ty     => Binder.Typ),
                              Typ      =>
                                Get_Typ (Binder.Discrs.Binder.B_Name)));
                     else
                        Result := Sequence
                          (Result, New_Assume_Statement
                             (Ada_Node => Ada_Node,
                              Pred     => +New_Comparison
                                (Symbol => Why_Eq,
                                 Left   => +Binder.Discrs.Binder.B_Name,
                                 Right  => +New_Discriminants_Access
                                   (Domain => EW_Term,
                                    Name   => Tmp,
                                    Ty     => Binder.Typ),
                                 Domain => EW_Pred)));
                     end if;
                  end if;

                  Result := +Binding_For_Temp (Ada_Node => Ada_Node,
                                               Domain   => Domain,
                                               Tmp      => Tmp,
                                               Context  => +Result);
               end;

            when Pointer =>
               declare
                  Binder_Typ : constant Entity_Id :=
                    Etype (Binder.Value.Ada_Node);
                  Tmp        : constant W_Expr_Id :=
                    New_Temp_For_Expr (+Right_Side);

               begin
                  pragma Assert
                    (No (Last_Access)
                     or else Nkind (Last_Access) = N_Explicit_Dereference);

                  Result := Sequence
                    (Result, New_Assignment
                       (Ada_Node => Ada_Node,
                        Name     => Binder.Value.B_Name,
                        Labels   => Symbol_Sets.Empty_Set,
                        Value    => +New_Pointer_Value_Access
                          (Ada_Node => Empty,
                           Domain   => EW_Pterm,
                           Name     => Tmp,
                           E        => Binder_Typ),
                        Typ      => Get_Typ (Binder.Value.B_Name)));

                  --  Address, is_null and is_moved cannot have been updated if
                  --  the last access was a dereference.

                  if Binder.Mutable and then No (Last_Access) then
                     Result := Sequence
                       ((1 => Result,
                         2 => New_Assignment
                          (Ada_Node => Ada_Node,
                           Name     => Binder.Address,
                           Labels   => Symbol_Sets.Empty_Set,
                           Value    => +New_Pointer_Address_Access
                             (Name => Tmp,
                              E    => Binder_Typ),
                           Typ      => Get_Typ (Binder.Address)),
                         3 => New_Assignment
                          (Ada_Node => Ada_Node,
                           Name     => Binder.Is_Null,
                           Labels   => Symbol_Sets.Empty_Set,
                           Value    => +New_Pointer_Is_Null_Access
                             (Name => Tmp,
                              E    => Binder_Typ),
                           Typ      => Get_Typ (Binder.Is_Null)),
                         4 => New_Assignment
                          (Ada_Node => Ada_Node,
                           Name     => Binder.Is_Moved,
                           Labels   => Symbol_Sets.Empty_Set,
                           Value    => +New_Pointer_Is_Moved_Access
                             (Name => Tmp,
                              E    => Binder_Typ),
                           Typ      => Get_Typ (Binder.Is_Moved))));
                  end if;

                  Result := +Binding_For_Temp (Ada_Node => Ada_Node,
                                               Domain   => Domain,
                                               Tmp      => Tmp,
                                               Context  => +Result);
               end;

            when Func
               | Concurrent_Self
            =>
               raise Program_Error;
            end case;
         end;
      end if;

      return Result;
   end New_Assignment;

   ------------------------
   -- New_Binary_Op_Expr --
   ------------------------

   function New_Binary_Op_Expr
     (Op          : N_Binary_Op;
      Left        : W_Expr_Id;
      Right       : W_Expr_Id;
      Left_Type   : Entity_Id;
      Right_Type  : Entity_Id;
      Return_Type : Entity_Id;
      Domain      : EW_Domain;
      Ada_Node    : Node_Id := Empty) return W_Expr_Id
   is
      Left_Rep  : W_Expr_Id := Left;
      Right_Rep : W_Expr_Id := Right;
      Base      : W_Type_Id := Why_Empty;
      T         : W_Expr_Id;

   begin
      case Op is
         when N_Op_Compare
            | N_Op_And
            | N_Op_Or
            | N_Op_Xor
            | N_Op_Concat
            | N_Op_Shift
         =>
            raise Program_Error;

         when N_Op_Add
            | N_Op_Subtract
         =>
            Base := Base_Why_Type (Left_Type, Right_Type);

            declare
               Name : constant W_Identifier_Id :=
                 (if Op = N_Op_Add then
                    (if Base = EW_Int_Type then Int_Infix_Add
                     elsif Why_Type_Is_BitVector (Base) then
                       MF_BVs (Base).Add
                     elsif Why_Type_Is_Fixed (Base) then Fixed_Infix_Add
                     else MF_Floats (Base).Add)
                  else
                    (if Base = EW_Int_Type then Int_Infix_Subtr
                     elsif Why_Type_Is_BitVector (Base) then
                          MF_BVs (Base).Sub
                     elsif Why_Type_Is_Fixed (Base) then Fixed_Infix_Subtr
                     else MF_Floats (Base).Subtr));
            begin
               Left_Rep :=
                 Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                           Domain   => Domain,
                                           Expr     => Left,
                                           To       => Base);
               Right_Rep :=
                 Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                           Domain   => Domain,
                                           Expr     => Right,
                                           To       => Base);

               if Has_Modular_Integer_Type (Return_Type)
                 and then Non_Binary_Modulus (Return_Type)
               then
                  T := Transform_Non_Binary_Modular_Operation
                    (Ada_Node   => Ada_Node,
                     Ada_Type   => Return_Type,
                     Domain     => Domain,
                     Op         => Op,
                     Left_Opnd  => Left_Rep,
                     Right_Opnd => Right_Rep,
                     Rep_Type   => Base,
                     Modulus    => Modulus (Return_Type));

               else
                  T :=
                    New_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => Name,
                       Args     => (1 => Left_Rep,
                                    2 => Right_Rep),
                       Typ   => Base);
                  T := Apply_Modulus (Op, Return_Type, T, Domain);
               end if;
            end;

         when N_Op_Multiply =>
            declare
               L_Type, R_Type : W_Type_Id;
               Oper           : Why_Name_Enum := WNE_Empty;

            begin
               --  Look for the appropriate base scalar type

               if Has_Fixed_Point_Type (Left_Type)
                 and then Has_Fixed_Point_Type (Right_Type)
               then
                  L_Type := Base_Why_Type (Left_Type);
                  R_Type := Base_Why_Type (Right_Type);
                  Oper := WNE_Fixed_Point_Mult;

                  if Has_Fixed_Point_Type (Return_Type) then
                     Base := Base_Why_Type (Return_Type);
                  else
                     pragma Assert (Has_Integer_Type (Return_Type));
                     Base := EW_Int_Type;
                  end if;

               elsif Has_Fixed_Point_Type (Left_Type) then
                  L_Type :=  Base_Why_Type (Left_Type);
                  R_Type := EW_Int_Type;
                  Base := Base_Why_Type (Return_Type);
                  Oper := WNE_Fixed_Point_Mult_Int;
                  pragma Assert (L_Type = Base);

               --  If multiplying an integer and a fixed-point, swap
               --  arguments so that Left is the fixed-point one.

               elsif Has_Fixed_Point_Type (Right_Type) then
                  L_Type    := Base_Why_Type (Right_Type);
                  R_Type    := EW_Int_Type;
                  Left_Rep  := Right;
                  Right_Rep := Left;
                  Base      := Base_Why_Type (Return_Type);
                  Oper      := WNE_Fixed_Point_Mult_Int;
                  pragma Assert (L_Type = Base);

               else
                  Base := Base_Why_Type (Left_Type, Right_Type);
                  L_Type := Base;
                  R_Type := Base;
                  pragma Assert (not Has_Fixed_Point_Type (Return_Type));
               end if;

               Left_Rep := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Left_Rep,
                  To       => L_Type);
               Right_Rep := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Right_Rep,
                  To       => R_Type);

               --  Construct the operation

               if Has_Fixed_Point_Type (Left_Type)
                 or else Has_Fixed_Point_Type (Right_Type)
               then
                  declare
                     pragma Assert (Oper /= WNE_Empty);
                     Name   : W_Identifier_Id;
                  begin
                     case Oper is
                        when WNE_Fixed_Point_Mult =>
                           Name := Get_Fixed_Point_Mult_Div_Theory
                             (Typ_Left   => Left_Type,
                              Typ_Right  => Right_Type,
                              Typ_Result => Return_Type).Mult;

                        when WNE_Fixed_Point_Mult_Int =>
                           Name := Get_Fixed_Point_Theory
                             (Typ => Return_Type).Mult_Int;

                        when others =>
                           raise Program_Error;
                     end case;

                     T := New_Call (Ada_Node => Ada_Node,
                                    Domain   => Domain,
                                    Name     => Name,
                                    Args     => (1 => Left_Rep,
                                                 2 => Right_Rep),
                                    Typ      => Base);
                  end;

               elsif Has_Modular_Integer_Type (Return_Type)
                 and then Non_Binary_Modulus (Return_Type)
               then
                  T := Transform_Non_Binary_Modular_Operation
                    (Ada_Node   => Ada_Node,
                     Ada_Type   => Return_Type,
                     Domain     => Domain,
                     Op         => Op,
                     Left_Opnd  => Left_Rep,
                     Right_Opnd => Right_Rep,
                     Rep_Type   => Base,
                     Modulus    => Modulus (Return_Type));

               else
                  declare
                     Name : constant W_Identifier_Id :=
                       (if Base = EW_Int_Type then Int_Infix_Mult
                        elsif Why_Type_Is_BitVector (Base) then
                          MF_BVs (Base).Mult
                        elsif Why_Type_Is_Fixed (Base) then Fixed_Infix_Mult
                        else MF_Floats (Base).Mult);
                  begin
                     T :=
                       New_Call
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Name     => Name,
                          Args     => (1 => Left_Rep, 2 => Right_Rep),
                          Typ      => Base);
                  end;
                  T := Apply_Modulus (Op, Return_Type, T, Domain);
               end if;

               if Base_Why_Type (Return_Type) /= Base then
                  T := Insert_Checked_Conversion
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Expr     => T,
                     To       => Base_Why_Type (Return_Type));
               end if;
            end;

         when N_Op_Divide =>
            declare
               Oper           : Why_Name_Enum := WNE_Empty;
               Name           : W_Identifier_Id;
               L_Type, R_Type : W_Type_Id;

            begin
               --  Look for the appropriate base scalar type

               if Has_Fixed_Point_Type (Left_Type)
                 and then Has_Fixed_Point_Type (Right_Type)
               then
                  L_Type := Base_Why_Type (Left_Type);
                  R_Type := Base_Why_Type (Right_Type);
                  Oper   := WNE_Fixed_Point_Div;

                  if Has_Fixed_Point_Type (Return_Type) then
                     Base := Base_Why_Type (Return_Type);
                  else
                     pragma Assert (Has_Integer_Type (Return_Type));
                     Base := EW_Int_Type;
                  end if;

               elsif Has_Fixed_Point_Type (Left_Type) then
                  Base   := Base_Why_Type (Return_Type);
                  L_Type := Base_Why_Type (Left_Type);
                  R_Type := EW_Int_Type;
                  Oper   := WNE_Fixed_Point_Div_Int;
                  pragma Assert (L_Type = Base);

               else
                  pragma Assert (not Has_Fixed_Point_Type (Return_Type));
                  Base   := Base_Why_Type (Left_Type, Right_Type);
                  L_Type := Base;
                  R_Type := Base;
               end if;

               pragma Assert
                 (if Has_Fixed_Point_Type (Return_Type)
                    or else Has_Fixed_Point_Type (Left_Type)
                  then Oper /= WNE_Empty);

               --  Construct the operation

               case Oper is
                  when WNE_Fixed_Point_Div =>
                     Name := Get_Fixed_Point_Mult_Div_Theory
                       (Typ_Left   => Left_Type,
                        Typ_Right  => Right_Type,
                        Typ_Result => Return_Type).Div;

                  when WNE_Fixed_Point_Div_Int =>
                     Name := Get_Fixed_Point_Theory
                       (Typ => Return_Type).Div_Int;

                  when others =>
                     Name := New_Division (Base);
               end case;

               Left_Rep := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Left,
                  To       => L_Type);
               Right_Rep := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Right,
                  To       => R_Type);

               if Domain = EW_Prog
                 and then Present (Ada_Node)
                 and then Do_Division_Check (Ada_Node)
               then
                  T :=
                    New_VC_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => To_Program_Space (Name),
                       Progs    => (1 => Left_Rep, 2 => Right_Rep),
                       Reason   => VC_Division_Check,
                       Typ      => Base);
               else
                  T :=
                    New_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => Name,
                       Args     => (1 => Left_Rep, 2 => Right_Rep),
                       Typ      => Base);
               end if;

               if Base_Why_Type (Return_Type) /= Base then
                  T := Insert_Checked_Conversion
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Expr     => T,
                     To       => Base_Why_Type (Return_Type));
               end if;
            end;

         when N_Op_Rem
            | N_Op_Mod
         =>
            declare
               Base : constant W_Type_Id :=
                 Base_Why_Type (Left_Type, Right_Type);
               Name : W_Identifier_Id;

            begin
               Name := (if Why_Type_Is_BitVector (Base) then
                          MF_BVs (Base).Urem
                        elsif Op = N_Op_Rem then
                          M_Int_Div.Rem_Id
                        else M_Int_Div.Mod_Id);

               Name := (if Domain = EW_Prog then
                          To_Program_Space (Name)
                        else
                          Name);
               T :=
                 New_VC_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => Name,
                    Progs    =>
                      (1 => Insert_Simple_Conversion
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Expr     => Left,
                          To       => Base),
                       2 => Insert_Simple_Conversion
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Expr     => Right,
                          To       => Base)),
                    Reason   => VC_Division_Check,
                    Typ      => Base);
            end;

         when N_Op_Expon =>
            declare
               Name : W_Identifier_Id;
               Typ  : constant W_Type_Id := Base_Why_Type (Left_Type);
               Base : constant W_Expr_Id :=
                 New_Temp_For_Expr
                   (Insert_Simple_Conversion
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Expr     => Left,
                       To       => Typ));
               Expo : constant W_Expr_Id :=
                 New_Temp_For_Expr
                   (Insert_Simple_Conversion
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Expr     => Right,
                       To       => EW_Int_Type));
            begin
               if Has_Modular_Integer_Type (Return_Type)
                 and then Non_Binary_Modulus (Return_Type)
               then
                  T := Transform_Non_Binary_Modular_Operation
                    (Ada_Node   => Ada_Node,
                     Ada_Type   => Return_Type,
                     Domain     => Domain,
                     Op         => Op,
                     Left_Opnd  => Base,
                     Right_Opnd => Expo,
                     Rep_Type   => Typ,
                     Modulus    => Modulus (Return_Type));

               else
                  Name := New_Exp (Typ);

                  T := New_Call
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Name     => Name,
                     Args     => (1 => Base, 2 => Expo),
                     Typ      => Typ);

                  T := Apply_Modulus (Op, Return_Type, T, Domain);

                  --  Exponentiation on floats can actually cause a division
                  --  check, when the base is 0 and the exponent is negative.

                  if Domain = EW_Prog
                    and then Is_Floating_Point_Type (Left_Type)
                  then
                     declare
                        Expo_Negative : constant W_Pred_Id :=
                          +New_Comparison
                          (Int_Infix_Lt, Expo,
                           New_Integer_Constant (Value => Uint_0), EW_Term);
                        Base_Zero     : constant W_Pred_Id :=
                          +New_Comparison
                          (Why_Neq, Base, +MF_Floats (Typ).Plus_Zero, EW_Term);
                        Ass           : constant W_Prog_Id :=
                          New_Located_Assert
                            (Ada_Node => Ada_Node,
                             Pred     =>
                               +New_Simpl_Conditional
                               (Domain    => EW_Pred,
                                Condition => +Expo_Negative,
                                Then_Part => +Base_Zero,
                                Else_Part => +True_Pred
                               ),
                             Reason   => VC_Division_Check,
                             Kind     => EW_Assert);
                     begin
                        T := +Sequence (Ass, +T);
                     end;
                  end if;
               end if;

               T := Binding_For_Temp (Ada_Node, Domain, Base, T);
               T := Binding_For_Temp (Ada_Node, Domain, Expo, T);
            end;
      end case;

      if Domain = EW_Prog
        and then Op in N_Op_Add | N_Op_Subtract | N_Op_Multiply
        and then Has_No_Wrap_Around_Annotation (Return_Type)
      then
         declare
            Check : constant W_Prog_Id :=
              Check_No_Wrap_Around_Modular_Operation
                (Ada_Node   => Ada_Node,
                 Ada_Type   => Return_Type,
                 Op         => Op,
                 Left_Opnd  => Left_Rep,
                 Right_Opnd => Right_Rep,
                 Rep_Type   => Base,
                 Modulus    => Modulus (Return_Type));
         begin
            T := +Sequence (Check, +T);
         end;
      end if;

      return T;
   end New_Binary_Op_Expr;

   ------------------------------------
   -- New_Constrained_Attribute_Expr --
   ------------------------------------

   function New_Constrained_Attribute_Expr
     (Prefix : Node_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Var : Node_Id := Prefix;

   begin
      --  Prefix can be either an object, a type, or a conversion of an object
      --  (when it is called on an actual parameter). In the latter case, the
      --  constrained attribute is the attribute of the converted object.

      while Nkind (Var) in N_Type_Conversion loop
         Var := Expression (Var);
      end loop;

      if Attr_Constrained_Statically_Known (Var) then
         return New_Literal
           (Domain => Domain,
            Value  =>
              (if Attribute_Constrained_Static_Value (Var)
               then EW_True else EW_False));
      else
         declare
            Binder : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, Entity (Var));
         begin
            if Binder.Constr.Present then
               return +Binder.Constr.Id;
            else
               return +False_Term;
            end if;
         end;
      end if;
   end New_Constrained_Attribute_Expr;

   ------------------------------------
   -- New_Pledge_Def_From_Expression --
   ------------------------------------

   function New_Pledge_Def_From_Expression
     (Brower      : Entity_Id;
      Borrowed_Id : out W_Identifier_Id;
      Brower_Id   : out W_Identifier_Id;
      Path        : Node_Id) return W_Term_Id
   is

      function Create_Pledge_Call_For_Prefix
        (Borrowed_Id  : out W_Identifier_Id;
         Brower_Id    : W_Identifier_Id;
         Path         : in out Node_Id;
         In_Traversal : Boolean := False) return W_Expr_Id;
      --  The path Path corresponds to a borrow (rooted at the borrowed
      --  entity Borrowed) or a reborrow (rooted at the borrower entity
      --  Brower).
      --  This function traverses the path Path until it finds either the root
      --  or a call to a traversal function. It generates a new identifier
      --  corresponding to the expression borrowed in the path (either the
      --  borrowed entity if we have reached the root or the first parameter of
      --  the traversal function call otherwise) and stores it in Borrowed_Id.
      --  After the call, Path contains what remains to be traversed: either
      --  the root, or the traversal function call.
      --  It returns a call relating at all time (time of pledge), the value
      --  of the borrower (represented by the identifier brower_id given as a
      --  parameter) and the value of expression borrowed in the traversed
      --  prefixed (represented by the identifier borrowed_id computed by the
      --  call).
      --  If In_Traversal is True, then the whole borrowed entity is considered
      --  to be frozen by the borrow, and not only the borrowed expression.

      procedure Wrap_Pledge_Call
        (W_Id : W_Identifier_Id;
         Expr : W_Expr_Id;
         Ty   : Entity_Id;
         Def  : in out W_Expr_Id);
      --  Introduce an existential quantification to link W_Id in Def.
      --  Expr is the expression for W_Id at the time of borrow and Ty is its
      --  Ada type. They will be used to assume the value of the is_null
      --  field of the existentially quantified variable.
      --  We generate:
      --
      --    exists w_id. w_id.is_null = expr.is_null /\ def

      -----------------------------------
      -- Create_Pledge_Call_For_Prefix --
      -----------------------------------

      function Create_Pledge_Call_For_Prefix
        (Borrowed_Id  : out W_Identifier_Id;
         Brower_Id    : W_Identifier_Id;
         Path         : in out Node_Id;
         In_Traversal : Boolean := False) return W_Expr_Id
      is
         Expr  : W_Expr_Id := +Brower_Id;
         Dummy : Node_Id := Path;
      begin
         --  We traverse prefixes of Path until we find the root or a function
         --  call constructing along the way in Expr an expression which stands
         --  for the value of Path'Old at the time of borrow updated at path
         --  Path by brower_id.

         while Nkind (Path) not in
           N_Identifier | N_Expanded_Name | N_Function_Call
         loop
            Shift_Rvalue (N           => Path,
                          Expr        => Expr,
                          Last_Access => Dummy,
                          Domain      => EW_Term);
         end loop;

         --  From a path F_1 (Args).Path where Path does not contain
         --  any traversal function calls, we generate:
         --
         --  get (f_1__pledge args ...)       (* the pledge of the call *)
         --      borrowed_id                  (* a new identifier standing for
         --                                      expr at the time of pledge *)
         --      { (f_1 args ...)             (* the result of the call at the
         --                                      time of borrow *)
         --          with path1 = brower_id } (* updated at path with the
         --                                      borrower at the time of pledge
         --                                    *)

         if Nkind (Path) = N_Function_Call then

            declare
               Subp     : constant Entity_Id := Get_Called_Entity (Path);
               Context  : Ref_Context;
               Store    : constant W_Statement_Sequence_Unchecked_Id :=
                 New_Unchecked_Statement_Sequence;
               Args     : constant W_Expr_Array :=
                 Compute_Call_Args
                   (Call    => Path,
                    Domain  => EW_Term,
                    Context => Context,
                    Store   => Store,
                    Params  => Body_Params);
               pragma Assert (Context.Length = 0);

            begin
               --  If we have found a function call, the borrowed identifier
               --  will represent the first parameter of the call.

               Borrowed_Id :=
                 New_Temp_Identifier
                   (Typ       => Type_Of_Node (Etype (First_Formal (Subp))),
                    Base_Name => "borrowed");

               return +New_And_Expr
                 (Left   => New_Pledge_Call (Subp, Args, +Borrowed_Id, Expr),
                  Right  => +Boolean_Term_Of_Pred
                    (Compute_Dynamic_Invariant
                         (Expr        => +Borrowed_Id,
                          Ty          => Etype (First_Formal (Subp)),
                          Params      => Body_Params,
                          Initialized => True_Term,
                          Only_Var    => False_Term)),
                  Domain => EW_Term);
            end;

         --  From a path Brower.Path where Path does not contain any traversal
         --  function calls, we generate:
         --
         --  get brower__pledge               (* the pledge of the borrower
         --                                      before the update *)
         --      borrowed_id                  (* a new identifier standing for
         --                                      the borrowed entity at the
         --                                      time of pledge *)
         --      { brower                     (* the borrower before the update
         --                                    *)
         --           with path = brower_id } (* updated at path with the value
         --                                      of the borrower at the time of
         --                                      pledge *)

         elsif Entity (Path) = Brower then

            --  We have a reborrow, Borrowed_id represents the borrowed entity

            Borrowed_Id :=
              New_Temp_Identifier
                (Typ       => Type_Of_Node
                   (Etype (Get_Borrowed_Entity (Brower))),
                 Base_Name => "borrowed");

            return New_Pledge_Call (Brower, +Borrowed_Id, Expr, True);

         --  Otherwise, we have a path Borrowed.Path where Path does not
         --  contain any traversal function calls. If we are in a traversal
         --  function, the borrowed entity has been frozen by the call, so we
         --  can generate:
         --
         --  borrowed_id =                    (* the borrower at the time of
         --                                      pledge *)
         --      { borrowed                   (* the borrowed entity at the
         --                                      time of borrow *)
         --           with path = brower_id } (* updated at path with the value
         --                                      of the borrower at the time of
         --                                      pledge *)

         elsif In_Traversal then

            --  Borrowed_Id represents the root of the path

            Borrowed_Id :=
              New_Temp_Identifier
                (Typ       => Type_Of_Node (Etype (Entity (Path))),
                 Base_Name => "borrowed");

            return New_Comparison
              (Symbol => Why_Eq,
               Left   => +Insert_Simple_Conversion
                 (Domain => EW_Term,
                  Expr   => Expr,
                  To     => Get_Typ (Borrowed_Id)),
               Right  => +Borrowed_Id,
               Domain => EW_Term);

         --  If we are not in a traversal function, it would be incorrect to
         --  generate:
         --    borrowed_id = { borrowed with path = brower_id }
         --  like before, as other components of borrowed are not frozen by the
         --  borrow and can be updated simultaneously. So we generate:
         --
         --  brower_id =           (* the borrower at the time of pledge *)
         --      borrowed_id.path  (* the part corresponding to path in a new
         --                           identifier standing for the borrowed
         --                           entity at the time of pledge *)

         else
            declare
               Borrowed   : constant Entity_Id := Entity (Path);
               Borrowed_E : W_Expr_Id;

            begin
               --  Borrowed_Id represents the root of the path

               Borrowed_Id :=
                 New_Temp_Identifier
                   (Typ       => Type_Of_Node (Etype (Borrowed)),
                    Base_Name => "borrowed");

               Ada_Ent_To_Why.Push_Scope (Symbol_Table);
               Insert_Entity (Borrowed, Borrowed_Id);
               Borrowed_E := +Insert_Simple_Conversion
                 (Domain => EW_Term,
                  Expr   => Transform_Expr
                    (Expr    => Get_Borrowed_Expr (Brower),
                     Domain  => EW_Term,
                     Params  => Body_Params),
                  To     => Type_Of_Node (Get_Borrowed_Typ (Brower)));
               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

               return New_Comparison (Symbol => Why_Eq,
                                      Left   => Borrowed_E,
                                      Right  => +Brower_Id,
                                      Domain => EW_Term);
            end;
         end if;
      end Create_Pledge_Call_For_Prefix;

      ----------------------
      -- Wrap_Pledge_Call --
      ----------------------

      procedure Wrap_Pledge_Call
        (W_Id : W_Identifier_Id;
         Expr : W_Expr_Id;
         Ty   : Entity_Id;
         Def  : in out W_Expr_Id)
      is
         --  Store in guard the fact that the is_null field match, as this
         --  is required to use the pledge later.

         Guard : constant W_Pred_Id := +New_Comparison
           (Symbol => Why_Eq,
            Left   => New_Pointer_Is_Null_Access (Ty, Expr),
            Right  => New_Pointer_Is_Null_Access (Ty, +W_Id),
            Domain => EW_Pred);
      begin
         Def :=
           +Boolean_Term_Of_Pred
           (New_Existential_Quantif
              (Variables => (1 => W_Id),
               Labels    => Symbol_Sets.Empty_Set,
               Var_Type  => Get_Typ (W_Id),
               Pred      => +New_And_Expr
                 (Left   => +Guard,
                  Right  => +Pred_Of_Boolean_Term (+Def),
                  Domain => EW_Pred)));
      end Wrap_Pledge_Call;

      --  Local variables

      In_Traversal : constant Boolean :=
        Ekind (Brower) = E_Function or else Is_Constant_Borrower (Brower);
      --  We are inside a traversal function if Brower is a function or if it
      --  is a constant borrower.

      Current     : Node_Id := Path;
      Def         : W_Expr_Id := +True_Term;
      Current_Id  : W_Identifier_Id :=
        New_Temp_Identifier
          (Typ       => Type_Of_Node (Etype (Brower)),
           Base_Name => "brower");
      --  The identifier for the borrower Brower at the time of pledge

      Pledge_Call : W_Expr_Id;
      First_Call  : Boolean := True;
      Borrowed    : Entity_Id := Empty;

   --  Start of processing for New_Pledge_Def_From_Expression

   begin
      Brower_Id := Current_Id;

      --  We construct the definition of the pledge linking the borrower and
      --  the borrowed entities at the time of pledge by part. We conjoin
      --  them inside Def. When we introduce additional identifiers for
      --  borrowed entities in pledges of traversal function calls, we
      --  link them using existential quantifiers.

      loop
         Borrowed := Current;

         Pledge_Call := Create_Pledge_Call_For_Prefix
           (Borrowed_Id  => Borrowed_Id,
            Brower_Id    => Current_Id,
            Path         => Current,
            In_Traversal => In_Traversal);

         Def := New_And_Expr
           (Left   => Pledge_Call,
            Right  => Def,
            Domain => EW_Term);

         --  If we are not in the first iteration, Current_Id contains the
         --  value of the borrowed_id from previous iteration. We existentially
         --  quantify over it in Def.

         if not First_Call then
            Wrap_Pledge_Call
              (W_Id => Current_Id,
               Expr => Transform_Expr (Params   => Body_Params,
                                       Expr     => Borrowed,
                                       Domain   => EW_Term),
               Ty   => Retysp (Etype (Borrowed)),
               Def  => Def);
         end if;

         exit when Nkind (Current) in N_Expanded_Name | N_Identifier;

         pragma Assert (Nkind (Current) = N_Function_Call);
         First_Call := False;

         Current_Id := Borrowed_Id;
         Current := First_Actual (Current);
      end loop;

      --  In the return statement of a borrowing traversal function, we need to
      --  continue the reconstruction until the borrowed parameter is reached.

      if Ekind (Brower) = E_Function then
         declare
            B_Ent    : Entity_Id := Entity (Current);
            Borrowed : Entity_Id;
         begin
            while Ekind (B_Ent) /= E_In_Parameter loop
               Current_Id := Borrowed_Id;

               --  We use the pledge of the borrowed object to link it to its
               --  own root.

               Borrowed := Get_Borrowed_Entity (B_Ent);
               Borrowed_Id :=
                 New_Temp_Identifier
                   (Typ       => Type_Of_Node (Etype (Borrowed)),
                    Base_Name => "borrowed");

               Pledge_Call := New_Pledge_Call
                 (B_Ent, +Borrowed_Id, +Current_Id, True);

               Def := New_And_Expr
                 (Left   => Pledge_Call,
                  Right  => Def,
                  Domain => EW_Term);

               Wrap_Pledge_Call
                 (W_Id => Current_Id,
                  Expr => Transform_Identifier
                    (Params   => Body_Params,
                     Expr     => B_Ent,
                     Ent      => B_Ent,
                     Domain   => EW_Term),
                  Ty   => Retysp (Etype (B_Ent)),
                  Def  => Def);

               B_Ent := Borrowed;
            end loop;
         end;
      end if;

      return +Def;
   end New_Pledge_Def_From_Expression;

   ---------------------------------------
   -- New_Pledge_Update_From_Assignment --
   ---------------------------------------

   function New_Pledge_Update_From_Assignment
     (Brower : Entity_Id;
      Path   : Node_Id) return W_Prog_Id
   is
      Brower_Id   : W_Identifier_Id;
      Borrowed_Id : W_Identifier_Id;
      Def         : constant W_Term_Id := New_Pledge_Def_From_Expression
        (Brower      => Brower,
         Borrowed_Id => Borrowed_Id,
         Brower_Id   => Brower_Id,
         Path        => Path);
   begin
      return New_Pledge_Update (Brower, Borrowed_Id, Brower_Id, Def);
   end New_Pledge_Update_From_Assignment;

   ------------------------
   -- New_Predicate_Call --
   ------------------------

   function New_Predicate_Call
     (Ty     : Entity_Id;
      W_Expr : W_Term_Id;
      Params : Transformation_Params) return W_Pred_Id
   is
      Variables : Flow_Id_Sets.Set;

   begin
      Variables_In_Dynamic_Predicate (Ty, Variables);

      declare
         Vars  : constant W_Expr_Array :=
           Get_Args_From_Variables (Variables, Params.Ref_Allowed);
         Num_B : constant Positive := 1 + Vars'Length;
         Args  : W_Expr_Array (1 .. Num_B);

      begin
         Args (1)          := +W_Expr;
         Args (2 .. Num_B) := Vars;

         return +New_Call (Name => E_Symb (Ty, WNE_Dynamic_Predicate),
                           Args => Args,
                           Typ  => EW_Bool_Type);
      end;
   end New_Predicate_Call;

   -------------------------
   -- New_Predicate_Check --
   -------------------------

   function New_Predicate_Check
     (Ada_Node         : Node_Id;
      Ty               : Entity_Id;
      W_Expr           : W_Expr_Id;
      On_Default_Value : Boolean := False) return W_Prog_Id
   is
      Check : constant W_Pred_Id :=
        Compute_Dynamic_Predicate (Expr    => +W_Expr,
                                   Ty      => Ty,
                                   Params  => Body_Params);
      Kind : constant VC_Kind :=
        (if On_Default_Value then
           VC_Predicate_Check_On_Default_Value
         else
           VC_Predicate_Check);
   begin
      return New_Assert
           (Pred        =>
                +New_VC_Expr (Ada_Node, +Check, Kind, EW_Pred),
            Assert_Kind => EW_Assert);
   end New_Predicate_Check;

   -----------------------------
   -- New_Type_Invariant_Call --
   -----------------------------

   function New_Type_Invariant_Call
     (Ty     : Entity_Id;
      W_Expr : W_Term_Id;
      Params : Transformation_Params) return W_Pred_Id
   is
      Variables : Flow_Id_Sets.Set;

   begin
      Variables_In_Type_Invariant (Ty, Variables);

      declare
         Vars  : constant W_Expr_Array :=
           Get_Args_From_Variables (Variables, Params.Ref_Allowed);
         Num_B : constant Positive := 1 + Vars'Length;
         Args  : W_Expr_Array (1 .. Num_B);

      begin
         Args (1)          := +W_Expr;
         Args (2 .. Num_B) := Vars;

         return +New_Call (Name => E_Symb (Ty, WNE_Type_Invariant),
                           Args => Args,
                           Typ  => EW_Bool_Type);
      end;
   end New_Type_Invariant_Call;

   -------------------------
   -- New_Invariant_Check --
   -------------------------

   function New_Invariant_Check
     (Ada_Node         : Node_Id;
      Ty               : Entity_Id;
      W_Expr           : W_Expr_Id;
      On_Default_Value : Boolean := False) return W_Prog_Id
   is
      Check : constant W_Pred_Id :=
        Compute_Type_Invariant (Expr         => +W_Expr,
                                Ty           => Ty,
                                Params       => Body_Params,
                                On_Internal  => True);
      Kind : constant VC_Kind :=
        (if On_Default_Value then
           VC_Invariant_Check_On_Default_Value
         else
           VC_Invariant_Check);
   begin
      if Is_True_Boolean (+Check) then
         return +Void;
      else
         return New_Assert
           (Pred        =>
              +New_VC_Expr (Ada_Node, +Check, Kind, EW_Pred),
            Assert_Kind => EW_Assert);
      end if;
   end New_Invariant_Check;

   ----------------------
   -- One_Level_Access --
   ----------------------

   function One_Level_Access
     (N      : Node_Id;
      Expr   : W_Expr_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id is
   begin
      case Nkind (N) is
         when N_Selected_Component =>
            declare
               Sel_Ent : constant Entity_Id := Entity (Selector_Name (N));
               Ty      : constant Entity_Id := Retysp (Etype (Prefix (N)));

               --  For private types, functions are declared in the first
               --  ancestor only

               R_Expr : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Ada_Node => N,
                    Domain   => EW_Term,
                    Expr     => Expr,
                    To       => (if Is_Init_Wrapper_Type (Get_Type (Expr))
                                 then EW_Init_Wrapper (Type_Of_Node (Ty))
                                 else Type_Of_Node (Ty)));
            begin
               return
                 New_Ada_Record_Access
                   (Ada_Node => N,
                    Domain   => Domain,
                    Name     => R_Expr,
                    Ty       => Ty,
                    Field    => Sel_Ent);
            end;

         when N_Explicit_Dereference =>
            declare
               Rec_Ty : constant Entity_Id := Retysp (Etype (Prefix (N)));
               R_Expr : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Ada_Node => N,
                                           Domain   => EW_Term,
                                           Expr     => Expr,
                                           To       => Type_Of_Node (Rec_Ty));
            begin
               return
                 +New_Pointer_Value_Access (Ada_Node => N,
                                            E        => Rec_Ty,
                                            Name     => R_Expr,
                                            Domain   => Domain);
            end;

         when N_Indexed_Component =>

            --  ??? Save the index in a temporary variable

            declare
               Ar      : constant Node_Id := Prefix (N);
               Ar_Tmp  : constant W_Expr_Id := New_Temp_For_Expr (Expr);
               Dim     : constant Pos := Number_Dimensions (Type_Of_Node (Ar));
               Indices : W_Expr_Array (1 .. Positive (Dim));
               Cursor  : Node_Id := First (Expressions (N));
               Count   : Positive := 1;
            begin
               while Present (Cursor) loop
                  Indices (Count) :=
                     Transform_Expr
                      (Cursor,
                       Base_Why_Type_No_Bool (Node_Id'(Type_Of_Node (Cursor))),
                       Domain,
                       Params);

                  --  Insert Index Check if needed

                  if Domain = EW_Prog and then Do_Range_Check (Cursor) then
                     Indices (Count) := +Do_Index_Check
                       (Ada_Node => Cursor,
                        Arr_Expr => Ar_Tmp,
                        W_Expr   => Indices (Count),
                        Dim      => Count);
                  end if;

                  Count := Count + 1;
                  Next (Cursor);
               end loop;

               return
                 +Binding_For_Temp (Domain => EW_Prog,
                                    Tmp    => Ar_Tmp,
                                    Context => New_Array_Access
                                      (Ada_Node => N,
                                       Domain   => Domain,
                                       Ar       => Ar_Tmp,
                                       Index    => Indices));
            end;

         when others =>
            Ada.Text_IO.Put_Line ("[One_Level_Access] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;
   end One_Level_Access;

   ----------------------
   -- One_Level_Update --
   ----------------------

   function One_Level_Update
     (N       : Node_Id;
      Pref    : W_Expr_Id;
      Value   : W_Expr_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id
   is

      --  In some cases, the frontend introduces an Itype for the type of a
      --  discriminant dependent component. In this case, to avoid a type
      --  mismatch in Why, we go to the root of the assignment to retrieve
      --  the correct type.

      Pref_Ty : constant Entity_Id :=
        (if Nkind (N) in N_Selected_Component | N_Indexed_Component | N_Slice
         then Expected_Type_Of_Prefix (Prefix (N))
         else Empty);
      Init_Val : constant W_Expr_Id :=
        (if Domain = EW_Prog
         and then Is_Init_Wrapper_Type (Get_Type (Value))
         and then not Expr_Has_Relaxed_Init (N)
         then Insert_Initialization_Check
           (Ada_Node               => N,
            E                      =>
              Get_Ada_Node (+Get_Type (Value)),
            Name                   => Value,
            Domain                 => EW_Prog,
            Exclude_Always_Relaxed => True)
         else Value);
      Result : W_Expr_Id;
   begin
      case Nkind (N) is
         when N_Selected_Component
            | N_Identifier
            | N_Expanded_Name
         =>
            --  In fact identifiers can refer to components in the case of
            --  protected objects. But this is the only case, and we assert
            --  this here.

            pragma Assert
              (if Nkind (N) in N_Identifier | N_Expanded_Name
               then Is_Protected_Component_Or_Discr_Or_Part_Of (Entity (N)));

            --  It can happen that the prefix does not have the expected type
            --  but some Itype with the same constraints. To avoid a type
            --  mismatch in Why, we should use the selector of the expected
            --  type instead.

            declare
               Selector  : constant Entity_Id :=
                 (if Nkind (N) in N_Identifier | N_Expanded_Name
                  then Entity (N)
                  else Search_Component_In_Type
                    (Pref_Ty, Entity (Selector_Name (N))));
               To_Type   : constant W_Type_Id :=
                 EW_Abstract
                   (Etype (Selector),
                    Relaxed_Init => Expr_Has_Relaxed_Init (N));
               New_Value : constant W_Expr_Id := Insert_Simple_Conversion
                      (Ada_Node => N,
                       Domain   => Domain,
                       Expr     => Init_Val,
                       To       => To_Type);
            begin
               --  The code should never update a discrimiant by assigning to
               --  it.

               pragma Assert (Ekind (Selector) /= E_Discriminant);

               Result := New_Ada_Record_Update
                 (Ada_Node => N,
                  Domain   => Domain,
                  Name     => Pref,
                  Field    => Selector,
                  Value    => New_Value);
            end;

         when N_Explicit_Dereference =>

            declare
               To_Type   : constant W_Type_Id := EW_Abstract
                 (Etype (N),
                  Relaxed_Init => Expr_Has_Relaxed_Init (N));
               New_Value : constant W_Expr_Id := Insert_Simple_Conversion
                 (Ada_Node => N,
                  Domain   => Domain,
                  Expr     => Init_Val,
                  To       => To_Type);

            begin
               Result := New_Ada_Pointer_Update
                 (Ada_Node => N,
                  Domain   => Domain,
                  Name     => Pref,
                  Value    => New_Value);
            end;

         when N_Indexed_Component =>
            declare
               Dim     : constant Pos := Number_Dimensions (Pref_Ty);
               Ar_Tmp  : constant W_Expr_Id := New_Temp_For_Expr (Pref);
               Indices : W_Expr_Array (1 .. Positive (Dim));
               Cursor  : Node_Id := First (Expressions (N));
               Count   : Positive := 1;
               To_Type : constant W_Type_Id := EW_Abstract
                 (Component_Type (Pref_Ty),
                  Relaxed_Init => Expr_Has_Relaxed_Init (N));
            begin
               while Present (Cursor) loop
                  Indices (Count) :=
                     Transform_Expr
                      (Cursor,
                       Base_Why_Type_No_Bool
                         (Entity_Id'(Type_Of_Node (Cursor))),
                       EW_Prog,
                       Params);

                  --  Insert Index Check if needed

                  if Domain = EW_Prog and then Do_Range_Check (Cursor) then
                     Indices (Count) := +Do_Index_Check
                       (Ada_Node => Cursor,
                        Arr_Expr => Ar_Tmp,
                        W_Expr   => Indices (Count),
                        Dim      => Count);
                  end if;

                  Count := Count + 1;
                  Next (Cursor);
               end loop;
               Result := +Binding_For_Temp
                 (Domain => EW_Prog,
                  Tmp    => Ar_Tmp,
                  Context => New_Array_Update
                    (Ada_Node  => N,
                     Ar        => Pref,
                     Index     => Indices,
                     Value     =>
                       Insert_Simple_Conversion
                         (Ada_Node => N,
                          Domain   => Domain,
                          Expr     => Init_Val,
                          To       => To_Type),
                     Domain    => Domain));
            end;

         when N_Slice =>
            declare
               Prefix_Name : constant W_Expr_Id :=
                 New_Temp_For_Expr (Pref, True);
               Value_Name  : constant W_Expr_Id :=
                 New_Temp_For_Expr (Init_Val, True);
               Dim     : constant Pos := Number_Dimensions (Pref_Ty);
               pragma Assert (Dim = 1);
               --  Slices are only for one-dimentional arrays (Ada RM 4.1.2)
               Result_Id   : constant W_Identifier_Id :=
                 New_Result_Ident (Get_Type (Pref));
               Binders_Type : constant W_Type_Id :=
                 Base_Why_Type_No_Bool (Discrete_Range (N));
               Binders     : constant W_Identifier_Array :=
                 New_Temp_Identifiers (Positive (Dim), Typ => Binders_Type);
               Indexes     : constant W_Expr_Array := To_Exprs (Binders);
               Range_Pred   : constant W_Expr_Id :=
                 Transform_Discrete_Choice
                   (Choice      => Discrete_Range (N),
                    Choice_Type => Empty,
                    Expr        => Indexes (1),
                    Domain      => EW_Pred,
                    Params      => Params);
               In_Slice_Eq  : constant W_Pred_Id :=
                 New_Element_Equality
                   (Left_Arr   => +Result_Id,
                    Right_Arr  => Value_Name,
                    Index      => Indexes);
               Unchanged    : constant W_Pred_Id :=
                 New_Element_Equality
                   (Left_Arr   => +Result_Id,
                    Right_Arr  => Prefix_Name,
                    Index      => Indexes);

               Def         : constant W_Pred_Id :=
                 New_Conditional
                   (Condition => Range_Pred,
                    Then_Part => +In_Slice_Eq,
                    Else_Part => +Unchanged);
               Quantif     : constant W_Expr_Id :=
                 New_Universal_Quantif
                   (Variables => Binders,
                    Var_Type  => Binders_Type,
                    Labels    => Symbol_Sets.Empty_Set,
                    Pred      => Def);

               --  If the prefix is not in split form, then its bounds are
               --  contained in the object. We should assume that they are
               --  preserved by the assignment.

               Bounds      : constant W_Pred_Id :=
                 (if Type_Get_Type_Kind (+Get_Type (Pref)) = EW_Abstract
                  then New_Bounds_Equality (Left_Arr  => Prefix_Name,
                                            Right_Arr => +Result_Id,
                                            Dim       => Positive (Dim))
                  else True_Pred);
            begin
               Result :=
                 +New_Simpl_Any_Prog (T    => Get_Type (Pref),
                                      Pred =>
                                        +New_And_Then_Expr
                                          (Left   => +Bounds,
                                           Right  => Quantif,
                                           Domain => EW_Pred));
               Result := Binding_For_Temp (Domain  => EW_Prog,
                                           Tmp     => Value_Name,
                                           Context => Result);
               Result := Binding_For_Temp (Domain  => EW_Prog,
                                           Tmp     => Prefix_Name,
                                           Context => Result);
            end;

         when others =>
            Ada.Text_IO.Put_Line ("[One_Level_Update] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;

      --  If the target type has a direct or inherited predicate, generate a
      --  corresponding check.

      declare
         Ty : constant Entity_Id := Get_Ada_Node (+Get_Type (Pref));
      begin
         if Domain = EW_Prog
           and then Present (Ty)
           and then Has_Predicates (Ty)
         then
            Result := +Insert_Predicate_Check
              (Ada_Node => N,
               Check_Ty => Ty,
               W_Expr   => +Result,
               Var_Ent  => Get_Ada_Node (+Pref));
         end if;
      end;

      return Result;
   end One_Level_Update;

   ----------------
   -- Range_Expr --
   ----------------

   function Range_Expr
     (N      : Node_Id;
      T      : W_Expr_Id;
      Domain : EW_Domain;
      Params : Transformation_Params;
      T_Type : W_Type_OId := Why_Empty) return W_Expr_Id
   is
      Subdomain  : constant EW_Domain :=
                     (if Domain = EW_Pred then EW_Term else Domain);
      Range_Node : constant Node_Id := Get_Range (N);
      Low        : constant Node_Id := Low_Bound (Range_Node);
      High       : constant Node_Id := High_Bound (Range_Node);
      Base_Type  : W_Type_Id := Base_Why_Type (Low, High);

      R : W_Expr_Id;

   begin
      if T_Type /= Why_Empty then
         Base_Type := Base_Why_Type (T_Type, Base_Type);
      end if;

      --  Another special case for booleans: The above base type computations
      --  return "bool" for Standard_Boolean, but in fact for a boolean range
      --  we still want to have "int" here.

      if Base_Type = EW_Bool_Type then
         Base_Type := EW_Int_Type;
      end if;

      declare
         Low_Expr : constant W_Expr_Id :=
           +Transform_Expr (Low, Base_Type, Subdomain, Params);
         High_Expr : constant W_Expr_Id :=
           +Transform_Expr (High, Base_Type, Subdomain, Params);
      begin
         R := New_Range_Expr
           (Domain    => Domain,
            Low       => Low_Expr,
            High      => High_Expr,
            Expr      => Insert_Simple_Conversion (Domain   => Subdomain,
                                                   Expr     => T,
                                                   To       => Base_Type));
      end;

      --  In programs, we generate a check that the range_constraint of a
      --  subtype_indication is compatible with the given subtype.

      if Domain = EW_Prog
        and then Nkind (N) = N_Subtype_Indication
      then
         R := +Sequence
           (Check_Subtype_Indication (Params   => Params,
                                      N        => N,
                                      Sub_Type => Etype (N)),
            +R);
      end if;

      return R;
   end Range_Expr;

   --------------------------------
   -- Reconstruct_Expr_From_Item --
   --------------------------------

   function Reconstruct_Expr_From_Item
     (Pattern   : Item_Type;
      Actual    : Node_Id;
      No_Checks : Boolean;
      Pre_Expr  : W_Expr_Id) return W_Prog_Id
   is
   begin
      case Pattern.Kind is
         when Concurrent_Self =>

            --  Here, we are necessarily in an external call.
            --  We need to reconstruct the object if it is mutable.

            pragma Assert (Pattern.Main.Mutable);
            declare
               Deref : constant W_Prog_Id :=
                 New_Deref (Right => Pattern.Main.B_Name,
                            Typ   => Get_Typ (Pattern.Main.B_Name));
            begin
               return +Insert_Checked_Conversion
                 (Ada_Node => Actual,
                  Domain   => (if No_Checks then EW_Pterm else EW_Prog),
                  Expr     => +Deref,
                  To       => Type_Of_Node (Actual));
            end;

         when Regular =>
            declare
               --  Types:

               Formal_T             : constant W_Type_Id :=
                 Get_Typ (Pattern.Main.B_Name);
               Actual_T             : constant W_Type_Id :=
                 Type_Of_Node (Actual);

               --  Variables:

               Deref                : constant W_Prog_Id :=
                 (if Pattern.Init.Present
                  then New_Label
                    (Labels => Symbol_Sets.Empty_Set,
                     Def    => New_Deref (Right => Pattern.Main.B_Name,
                                          Typ   => Formal_T),
                     Typ    => EW_Split (Get_Ada_Node (+Formal_T)))
                  else New_Deref (Right => Pattern.Main.B_Name,
                                  Typ   => Formal_T));
               --  The init flag is always true after the call. Go to the
               --  concrete type to avoid an unnecessary check.

               --  On store, checks are not inserted for composite
               --  parameters to avoid duplicate discriminant or length
               --  check. Predicate and initialization checks are introduced
               --  afterward.

               Need_Check_On_Store : constant Boolean :=
                 not No_Checks
                 and then Is_Scalar_Type (Retysp (Etype (Actual)));

            begin
               if Need_Check_On_Store then
                  return +Insert_Checked_Conversion
                    (Ada_Node => Actual,
                     Domain   => EW_Prog,
                     Expr     => +Deref,
                     Lvalue   => True,
                     To       =>
                       (if Is_Init_Wrapper_Type (Formal_T)
                        then EW_Init_Wrapper (Actual_T)
                        else Actual_T));
               else
                  return +Insert_Simple_Conversion
                    (Ada_Node => Actual,
                     Domain   => EW_Prog,
                     Expr     => +Deref,
                     To       =>
                       (if Is_Init_Wrapper_Type (Formal_T)
                        then EW_Init_Wrapper (Actual_T)
                        else Actual_T));
               end if;
            end;

         when UCArray =>
            declare
               --  Types:

               Formal_T           : constant W_Type_Id :=
                 Get_Typ (Pattern.Content.B_Name);
               Actual_T           : constant W_Type_Id :=
                 Type_Of_Node (Actual);
               Deref              : constant W_Prog_Id :=
                 New_Deref (Right => Pattern.Content.B_Name,
                            Typ   => Formal_T);

               --  If the argument is in split form, we
               --  need to reconstruct the argument using the actual's
               --  bounds before applying the conversion.

               Reconstructed_Arg : constant W_Prog_Id :=
                 (if Is_Static_Array_Type
                    (Get_Ada_Node (+Get_Why_Type_From_Item (Pattern)))
                  then +Deref
                  else +Array_Convert_From_Base
                    (EW_Prog, Pre_Expr, +Deref));

            begin
               --  Generate an expression of the form:
               --
               --    to_actual_type_ (from_formal_type (!tmp_var))

               return +Insert_Simple_Conversion
                 (Ada_Node => Actual,
                  Domain   => EW_Pterm,
                  Expr     => +Reconstructed_Arg,
                  To       =>
                    (if Is_Init_Wrapper_Type (Formal_T)
                     then EW_Init_Wrapper (Actual_T)
                     else Actual_T));
            end;

         when DRecord =>
            declare
               Formal_T : constant W_Type_Id :=
                 Get_Why_Type_From_Item (Pattern);

               Reconstructed_Arg : W_Prog_Id;
               --  We reconstruct the argument and convert it to the
               --  actual type (without checks). We store the result in
               --  Reconstructed_Arg.

               Arg_Array         : W_Expr_Array (1 .. 4);
               Index             : Positive := 1;

            begin
               --  For fields, use the temporary variable

               if Pattern.Fields.Present then
                  Arg_Array (Index) :=
                    New_Deref (Right => Pattern.Fields.Binder.B_Name,
                               Typ   =>
                                 Get_Typ (Pattern.Fields.Binder.B_Name));
                  Index := Index + 1;
               end if;

               --  If discriminants are mutable, we have introduced a
               --  temporary variable for them if we could not reuse the
               --  discriminants from the actual because they were not
               --  mutable. In this case, also assume preservation of the
               --  discriminants.

               if Pattern.Discrs.Present then
                  if Pattern.Discrs.Binder.Mutable then
                     declare
                        Discr_Name : constant W_Identifier_Id :=
                          Pattern.Discrs.Binder.B_Name;
                     begin
                        Arg_Array (Index) := New_Deref
                          (Right => Discr_Name,
                           Typ   => Get_Typ (Discr_Name));
                     end;
                  else
                     Arg_Array (Index) :=
                       New_Discriminants_Access
                         (Domain => EW_Prog,
                          Name   => Pre_Expr,
                          Ty     => Pattern.Typ);
                  end if;

                  Index := Index + 1;
               end if;

               if Pattern.Tag.Present then
                  Arg_Array (Index) :=
                    New_Tag_Access
                      (Domain => EW_Prog,
                       Name   => Pre_Expr,
                       Ty     => Pattern.Typ);

                  Index := Index + 1;
               end if;

               Reconstructed_Arg :=
                 +Record_From_Split_Form
                 (A            => Arg_Array (1 .. Index - 1),
                  Ty           => Pattern.Typ,
                  Init_Wrapper => Is_Init_Wrapper_Type (Formal_T));

               Reconstructed_Arg :=
                 +Insert_Simple_Conversion
                 (Domain   => EW_Pterm,
                  Expr     => +Reconstructed_Arg,
                  To       => EW_Abstract
                    (Etype (Actual),
                     Relaxed_Init =>
                       Is_Init_Wrapper_Type (Formal_T)));

               return Reconstructed_Arg;
            end;

         when Pointer =>
            declare
               Formal_Typ        : constant Entity_Id :=
                 Etype (Pattern.Value.Ada_Node);

               Reconstructed_Arg : W_Prog_Id;
               --  We reconstruct the argument and convert it to the
               --  actual type (without checks). We store the result
               --  in Reconstructed_Arg.

               Arg_Array         : W_Expr_Array (1 .. 4);

            begin
               --  For value, use the temporary variable

               Arg_Array (1) :=
                 New_Deref (Right => Pattern.Value.B_Name,
                            Typ   => Get_Typ (Pattern.Value.B_Name));

               --  If we have introduced temporary references for the
               --  address and is_null, use them.

               if Pattern.Mutable then
                  Arg_Array (2) :=
                    New_Deref (Right => Pattern.Address,
                               Typ   => Get_Typ (Pattern.Address));
                  Arg_Array (3) :=
                    New_Deref (Right => Pattern.Is_Null,
                               Typ   => Get_Typ (Pattern.Is_Null));

               --  The values from the actual have not been modified.
               --  Take them from Pre_Expr.

               else
                  Arg_Array (2) := New_Pointer_Address_Access
                    (Formal_Typ, Pre_Expr);
                  Arg_Array (3) := New_Pointer_Is_Null_Access
                    (Formal_Typ, Pre_Expr);
               end if;

               --  Always use is_moved from Pre_Expr

               Arg_Array (4) := New_Pointer_Is_Moved_Access
                 (Formal_Typ, Pre_Expr);

               Reconstructed_Arg :=
                 +Pointer_From_Split_Form
                 (A  => Arg_Array,
                  Ty => Formal_Typ);

               Reconstructed_Arg :=
                 +Insert_Simple_Conversion
                 (Domain   => EW_Pterm,
                  Expr     => +Reconstructed_Arg,
                  To       => EW_Abstract
                    (Etype (Actual),
                     Relaxed_Init =>
                       Is_Init_Wrapper_Type
                         (Get_Type (+Reconstructed_Arg))));

               return Reconstructed_Arg;
            end;
         when Func => raise Program_Error;
      end case;
   end Reconstruct_Expr_From_Item;

   -----------------------
   -- Reset_Map_For_Old --
   -----------------------

   procedure Reset_Map_For_Old is
   begin
      Old_Map.Clear;
   end Reset_Map_For_Old;

   ------------------
   -- Shift_Rvalue --
   ------------------

   procedure Shift_Rvalue
     (N           : in out Node_Id;
      Expr        : in out W_Expr_Id;
      Last_Access : in out Node_Id;
      Domain      : EW_Domain := EW_Prog)
   is
      Typ : Node_Id;
   begin
      case Nkind (N) is
         when N_Identifier
            | N_Expanded_Name
         =>
            null;

         --  We include a type qualification here even if it may not occur
         --  on the left-hand side of an assignment, due to the use of
         --  Shift_Rvalue on borrowed expressions, where a type qualification
         --  may appear.

         when N_Type_Conversion
            | N_Unchecked_Type_Conversion
            | N_Qualified_Expression
         =>
            N := Expression (N);
            Typ := Retysp (Etype (N));

            --  When performing copy back of parameters or due to inlining
            --  on GNATprove mode, left-hand side of assignment may contain
            --  a type conversion that must be checked. For non scalar
            --  types, do not use Insert_Checked_Conversion which introduces
            --  too many checks (bounds, discriminants).

            if Domain = EW_Prog and then Do_Range_Check (N) then
               Expr :=
                 +Insert_Checked_Conversion
                 (Ada_Node => N,
                  Domain   => EW_Prog,
                  Expr     => Expr,
                  To       => EW_Abstract
                    (Typ, Is_Init_Wrapper_Type (Get_Type (Expr))),
                  Lvalue   => True);
            else
               Expr :=
                 +Insert_Simple_Conversion
                 (Domain => Domain,
                  Expr   => Expr,
                  To     => EW_Abstract
                    (Typ, Is_Init_Wrapper_Type (Get_Type (Expr))));

               if Domain = EW_Prog and then Has_Predicates (Typ) then
                  Expr := +Insert_Predicate_Check
                    (Ada_Node => N,
                     Check_Ty => Typ,
                     W_Expr   => +Expr);
               end if;
            end if;

         when N_Selected_Component
            | N_Indexed_Component
            | N_Slice
            | N_Explicit_Dereference
         =>
            Last_Access := N;

            declare
               Prefix_Type : constant W_Type_Id :=
                 Expected_Type_Of_Prefix (Prefix (N));

               Subdomain  : constant EW_Domain :=
                 (if Domain = EW_Prog then EW_Pterm else Domain);
               --  We compute the expression for the Prefix in the EW_Term
               --  domain so that checks are not done for it as they are
               --  duplicates of those done in One_Level_Update.

               Prefix_Expr : constant W_Expr_Id :=
                 +Transform_Expr (Domain        => Subdomain,
                                  Expr          => Prefix (N),
                                  Expected_Type => Prefix_Type,
                                  Params        => Body_Params);
            begin
               Expr :=
                 One_Level_Update
                 (N,
                  +Prefix_Expr,
                  Expr,
                  Domain,
                  Params => Body_Params);
               N := Prefix (N);
            end;

         when others =>
            Ada.Text_IO.Put_Line ("[Shift_Rvalue] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;
   end Shift_Rvalue;

   -----------------------
   -- Transform_Actions --
   -----------------------

   function Transform_Actions
     (Actions : List_Id;
      Expr    : W_Expr_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id
   is
      T : W_Expr_Id;
      N : Node_Id;

      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);

   begin
      T := Expr;
      N := First (Actions);
      while Present (N) loop
         case Nkind (N) is

            --  Currently ignore type declarations in actions. A more precise
            --  treatment would factor out the code of Transform_Declaration
            --  to possibly generate an assumption here.

            when N_Subtype_Declaration
               | N_Full_Type_Declaration
            =>
               null;

            when N_Object_Declaration =>
               declare
                  E : constant Entity_Id := Defining_Identifier (N);
               begin
                  pragma Assert (Constant_Present (N));

                  T :=
                    New_Typed_Binding
                      (Domain  => Subdomain,
                       Name    =>
                         New_Identifier (Name => Full_Name (E)),
                       Def     =>
                         +Transform_Expr
                         (Expression (N),
                          Type_Of_Node (Etype (E)),
                          Subdomain,
                          Params),
                       Context => T);
               end;

            when N_Ignored_In_SPARK =>
               null;

            when N_Pragma =>
               if Is_Ignored_Pragma_Check (N) then
                  null;
               else
                  raise Program_Error;
               end if;

            when others =>
               raise Program_Error;
         end case;

         Next (N);
      end loop;

      return T;
   end Transform_Actions;

   -----------------------------------
   -- Transform_Actions_Preparation --
   -----------------------------------

   procedure Transform_Actions_Preparation
     (Actions : List_Id)
   is
      N  : Node_Id;
      Id : W_Identifier_Id;

   begin
      N := First (Actions);
      while Present (N) loop
         case Nkind (N) is

            --  Currently ignore type declarations in actions. A more precise
            --  treatment would factor out the code of Transform_Declaration
            --  to possibly generate an assumption here.

            when N_Subtype_Declaration
               | N_Full_Type_Declaration
            =>
               null;

            when N_Object_Declaration =>
               pragma Assert (Constant_Present (N));

               Id :=
                 New_Identifier
                   (Name => Full_Name (Defining_Identifier (N)),
                    Typ  => Type_Of_Node (Etype (Defining_Identifier (N))));

               Insert_Entity
                 (Defining_Identifier (N),
                  Id);

            when N_Ignored_In_SPARK =>
               null;

            when N_Pragma =>
               if Is_Ignored_Pragma_Check (N) then
                  null;
               else
                  raise Program_Error;
               end if;

            when others =>
               raise Program_Error;
         end case;

         Next (N);
      end loop;
   end Transform_Actions_Preparation;

   -------------------------
   -- Transform_Aggregate --
   -------------------------

   function Transform_Aggregate
     (Params        : Transformation_Params;
      Domain        : EW_Domain;
      Expr          : Node_Id;
      Update_Prefix : Node_Id := Empty) return W_Expr_Id
   is
      --  The aggregate is the argument of a 'Update attribute_reference or a
      --  delta aggregate if and only if Update_Prefix has been supplied.

      In_Delta_Aggregate : constant Boolean := Present (Update_Prefix);
      Expr_Typ           : constant Entity_Id := Type_Of_Node (Expr);
      Nb_Dim             : constant Positive :=
        (if Ekind (Expr_Typ) = E_String_Literal_Subtype then 1
         else Integer (Number_Dimensions (Expr_Typ)));
      Needs_Bounds       : constant Boolean :=
        not In_Delta_Aggregate and then not Is_Static_Array_Type (Expr_Typ);
      --  We do not need to give the array bounds as additional arguments to
      --  the aggregate function if it is a delta aggregate (we will use the
      --  bounds of the updated object) or if the type is static (the bounds
      --  are declared in the type).
      Init_Wrapper        : constant Boolean := Expr_Has_Relaxed_Init (Expr);

      -----------------------
      -- Local subprograms --
      -----------------------

      procedure Get_Aggregate_Elements
        (Expr         : Node_Id;
         Values       : out Node_Lists.List;
         Types        : out Node_Lists.List;
         Index_Values : out Node_Lists.List;
         Index_Types  : out Node_Lists.List);
      --  Extract parts of the aggregate Expr that will be passed in
      --  parameter to the logic function for the aggregate.
      --  Collect these parameters in Values, with the corresponding type
      --  stored at the same position in Types.
      --  For a normal aggregate each element of Values is an element of the
      --  (possibly multi-dimensional) aggregate.
      --  For a delta aggregate, the choice indexes are
      --  collected in Values in addition to the elements.
      --  For a normal aggregate, each element of Index_Values is a
      --  component_association whose choices need to be checked against
      --  the type at the same position in Base_Types.

      procedure Generate_Logic_Function
        (Expr   : Node_Id;
         Values : Node_Lists.List;
         Types  : Node_Lists.List);
      --  Generate the logic function definition for the aggregate Expr, with a
      --  suitable defining axiom:
      --
      --     function F (<params>) : <type of aggregate>
      --
      --     axiom A:
      --       forall id:<type of aggregate>. forall <params>.
      --         <proposition for the aggregate F(<params>)>

      function Transform_Array_Component_Associations
        (Expr   : Node_Id;
         Arr    : W_Expr_Id;
         Args   : Ada_Ent_To_Why.Map;
         Params : Transformation_Params) return W_Pred_Id;
      --  Generates the proposition defining the aggregate Arr, based on a
      --  mapping between Ada nodes and corresponding Why identifiers.

      function Complete_Translation
        (Params       : Transformation_Params;
         Domain       : EW_Domain;
         Func         : W_Identifier_Id;
         Values       : Node_Lists.List;
         Types        : Node_Lists.List;
         Index_Values : Node_Lists.List;
         Index_Types  : Node_Lists.List) return W_Expr_Id;
      --  Given a logic function Func previously defined for the aggregate,
      --  generate the actual call to Func by translating arguments Values
      --  of type Types in the context given by Params.

      procedure Insert_Check_For_Ranges (T : in out W_Expr_Id)
      with Pre => Domain = EW_Prog;
      --  Insert checks for range constraints

      --------------------------
      -- Complete_Translation --
      --------------------------

      function Complete_Translation
        (Params       : Transformation_Params;
         Domain       : EW_Domain;
         Func         : W_Identifier_Id;
         Values       : Node_Lists.List;
         Types        : Node_Lists.List;
         Index_Values : Node_Lists.List;
         Index_Types  : Node_Lists.List) return W_Expr_Id
      is
         use Node_Lists;

         Cnt      : Positive;
         Value    : Node_Lists.Cursor;
         Typ      : Node_Lists.Cursor;
         Args     : W_Expr_Array (1 .. Natural (Values.Length));
         Bnd_Args : W_Expr_Array
           (1 .. (if Needs_Bounds then 2 * Nb_Dim else 0));
         R        : W_Expr_Id;

      begin
         --  Compute the arguments for the function call

         Cnt   := 1;
         Value := Values.First;
         Typ   := Types.First;
         while Value /= No_Element loop
            Args (Cnt) :=
              Transform_Expr
                (Element (Value),
                 (if Expr_Has_Relaxed_Init (Element (Value), No_Eval => False)
                  then EW_Abstract (Element (Typ), Relaxed_Init => True)
                  else Type_Of_Node (Element (Typ))),
                 --  If a value which is not a scalar type has relaxed
                 --  initialization, so will the aggregate. Go to the wrapper
                 --  type to avoid spurious initialization checks.

                 Domain,
                 Params);

            --  Attributes of record array elements have default values

            if Has_Record_Type (Element (Typ))
              or else Full_View_Not_In_SPARK (Element (Typ))
            then
               Args (Cnt) := New_Tag_Update
                 (Domain   => Domain,
                  Name     => Args (Cnt),
                  Ty       => Element (Typ));
            end if;

            Next (Value);
            Next (Typ);
            Cnt := Cnt + 1;
         end loop;

         --  Compute the bounds of the type to be given as additional arguments
         --  to the aggregate function.

         if Needs_Bounds then
            for Dim in 1 .. Nb_Dim loop
               Bnd_Args (2 * Dim - 1) := Get_Array_Attr
                 (Domain, Etype (Expr), Attribute_First, Dim);
               Bnd_Args (2 * Dim) := Get_Array_Attr
                 (Domain, Etype (Expr), Attribute_Last, Dim);
            end loop;
         end if;

         --  If we are in a delta aggregate and we need checks, introduce
         --  a temporary for the updated expression so that it can be reused
         --  for checks of bounds of choices.

         if In_Delta_Aggregate and then Domain = EW_Prog then
            Args (1) := New_Temp_For_Expr (Args (1));
         end if;

         --  Compute the call

         R := New_Call (Ada_Node => Expr,
                        Domain   => Domain,
                        Name     => Func,
                        Args     => Args & Bnd_Args,
                        Typ      => Type_Of_Node (Expr));

         --  For delta aggregates, choices are passed as parameters and
         --  checks inserted in Transform_Expr when arguments for the
         --  function call are computed, above, so we don't need to check
         --  absence of RTE for them. We still need to check that choices are
         --  in the bounds of the updated expression. In the case of simple
         --  values of an array constrained type, this check may be redundant.

         if In_Delta_Aggregate and then Domain = EW_Prog then
            Value := Index_Values.First;
            Typ   := Index_Types.First;

            declare
               Checks : W_Statement_Sequence_Id := Void_Sequence;
               Choice : Node_Id;
               Tmp    : W_Identifier_Id;
            begin
               while Value /= No_Element loop
                  Choice := First (Choices (Element (Value)));
                  while Present (Choice) loop

                     --  For multidimensional 'Update, we generate an
                     --  index check for each value of the choice aggregate.
                     --  For (I1, I2) => ... we generate:
                     --  index_check <I1>; index_check <I2>

                     if Nb_Dim > 1 then
                        pragma Assert (Nkind (Choice) = N_Aggregate);
                        declare
                           Multi_Exprs      : constant List_Id :=
                             Expressions (Choice);
                           Multi_Expression : Node_Id :=
                             Nlists.First (Multi_Exprs);
                        begin
                           for I in 1 .. Nb_Dim loop
                              pragma Assert (Present (Multi_Expression));
                              Sequence_Append
                                (Checks,
                                 (New_Ignore
                                      (Prog => Do_Index_Check
                                         (Ada_Node => Multi_Expression,
                                          Arr_Expr => Args (1),
                                          W_Expr   => Transform_Expr
                                            (Expr          => Multi_Expression,
                                             Domain        => EW_Pterm,
                                             Params        => Params,
                                             Expected_Type =>
                                               Nth_Index_Rep_Type_No_Bool
                                                 (Expr_Typ, I)),
                                          Dim      => I))));
                              Next (Multi_Expression);
                           end loop;
                        end;

                     --  Choices of unary aggregates can involve ranges or
                     --  subtype indications in addition to values. We reuse
                     --  translation of choices to generate:
                     --  let index = any <Index_Type> { result in <Choice> } in
                     --    index_check index

                     else
                        Tmp := New_Temp_Identifier
                          (Base_Name => "index",
                           Typ       => Base_Why_Type_No_Bool (Element (Typ)));

                        Sequence_Append
                          (Checks,
                           (New_Ignore
                                (Prog => New_Binding
                                   (Name    => Tmp,
                                    Def     => New_Any_Expr
                                      (Post        =>
                                           +Transform_Discrete_Choice
                                         (Choice      => Choice,
                                          Choice_Type => Element (Typ),
                                          Expr        =>
                                            +New_Result_Ident (Get_Typ (Tmp)),
                                          Domain      => EW_Pred,
                                          Params      => Params),
                                       Return_Type => Get_Typ (Tmp),
                                       Labels      => Symbol_Sets.Empty_Set),
                                    Context => +Do_Index_Check
                                      (Ada_Node => Choice,
                                       Arr_Expr => Args (1),
                                       W_Expr   => +Tmp,
                                       Dim      => 1)))));
                     end if;
                     Next (Choice);
                  end loop;
                  Next (Value);
                  Next (Typ);
               end loop;
               R := +Sequence (+Checks, +R);

               R := Binding_For_Temp
                 (Domain  => EW_Prog,
                  Tmp     => Args (1),
                  Context => R);
            end;

         --  Special case for choices of normal aggregate:
         --  In programs, we generate a check that all the choices are
         --  compatible with their index subtype:
         --  . a non-static value of choice must belong to the index subtype
         --  . the range_constraint of a subtype_indication must be compatible
         --    with the given subtype.
         --  Note that checks are done with respect to the aggregate's type
         --  Etype, as the aggregate's Etype may not respect its parent's
         --  constraints.

         elsif not In_Delta_Aggregate and then Domain = EW_Prog then
            Value    := Index_Values.First;
            Typ      := Index_Types.First;

            declare
               Checks : W_Statement_Sequence_Id := Void_Sequence;
            begin
               while Value /= No_Element loop
                  Sequence_Append
                    (Checks,
                     (New_Ignore
                          (Prog =>
                             +Transform_Discrete_Choices
                             (Choices      => Choices (Element (Value)),
                              Choice_Type  => Element (Typ),
                              Matched_Expr =>
                              --  The value does not matter here
                                New_Discrete_Constant
                                  (Value => Uint_0,
                                   Typ   =>
                                     Base_Why_Type_No_Bool (Element (Typ))),
                              Cond_Domain  => EW_Prog,
                              Params       => Params))));
                  Next (Value);
                  Next (Typ);
               end loop;
               R := +Sequence (+Checks, +R);
            end;
         end if;

         --  If the aggregate has known bounds, we use this information if it
         --  is not contained in the type.

         if Domain = EW_Prog
           and then (Nkind (Expr) = N_Aggregate
                     and then Present (Aggregate_Bounds (Expr)))
           and then not Is_Static_Array_Type (Retysp (Etype (Expr)))
         then
            declare
               Temp   : constant W_Expr_Id := New_Temp_For_Expr (R, True);
               A1, A2 : W_Prog_Id;
               Typ    : constant Node_Id := First_Index
                 (Retysp (Etype (Etype (Expr))));
               W_Typ  : constant W_Type_Id :=
                 (if Typ = Empty then EW_Int_Type else
                     Base_Why_Type_No_Bool (Typ));
            begin
               A1 :=
                 New_Assume_Statement
                   (Pred =>
                      New_Call
                        (Name => Why_Eq,
                         Typ  => EW_Bool_Type,
                         Args =>
                           (1 =>
                            Get_Array_Attr (EW_Term, Temp, Attribute_First, 1),
                            2 =>
                              Transform_Expr
                                (Low_Bound (Aggregate_Bounds (Expr)),
                                 W_Typ,
                                 EW_Term,
                                 Params))));
               A2 :=
                 New_Assume_Statement
                   (Pred =>
                      New_Call
                        (Name => Why_Eq,
                         Typ  => EW_Bool_Type,
                         Args =>
                           (1 =>
                             Get_Array_Attr (EW_Term, Temp, Attribute_Last, 1),
                            2 =>
                              Transform_Expr
                                (High_Bound (Aggregate_Bounds (Expr)),
                                 W_Typ,
                                 EW_Term,
                                 Params))));
               R := +Sequence (A2, +Temp);
               R := +Sequence (A1, +R);
               R := Binding_For_Temp (Expr, EW_Prog, Temp, R);
            end;
         end if;

         --  Possibly check the predicate on the aggregate

         if Domain = EW_Prog
           and then Has_Predicates (Retysp (Etype (Expr)))
         then
            R := +Insert_Predicate_Check (Ada_Node => Expr,
                                          Check_Ty => Retysp (Etype (Expr)),
                                          W_Expr   => +R);
         end if;

         --  Insert checks for subtype indications in ranges in the aggregate

         if Domain = EW_Prog then
            Insert_Check_For_Ranges (R);
         end if;

         return R;
      end Complete_Translation;

      -----------------------------
      -- Generate_Logic_Function --
      -----------------------------

      procedure Generate_Logic_Function
        (Expr   : Node_Id;
         Values : Node_Lists.List;
         Types  : Node_Lists.List)
      is
         function Get_Name_For_Aggregate (Expr : Node_Id) return String;
         --  Return a suitable name for the aggregate Expr. If Expr is the
         --  initialization expression in an object declaration, then use the
         --  name of the object as basis, which ensures stable naming across
         --  changes in GNATprove. Otherwise, use a temporary name based on a
         --  counter.

         ----------------------------
         -- Get_Name_For_Aggregate --
         ----------------------------

         function Get_Name_For_Aggregate (Expr : Node_Id) return String is
            Obj : constant Entity_Id := Get_Initialized_Object (Expr);

         begin
            --  If Expr is used to initialize an object, reuse the object name
            --  to get a stable name.

            if Present (Obj) then
               return Get_Module_Name (E_Module (Obj))
                 & To_String (WNE_Aggregate_Def_Suffix);
            else
               return New_Temp_Identifier
                 (To_String (WNE_Aggregate_Def_Suffix));
            end if;
         end Get_Name_For_Aggregate;

         use Node_Lists;

         --  Generate name for the function based on the location of the
         --  aggregate.

         Name          : constant String :=
           Lower_Case_First (Get_Name_For_Aggregate (Expr));
         Module        : constant W_Module_Id :=
           New_Module
             (Ada_Node => Expr,
              File     => No_Symbol,
              Name     => Name);
         Func          : constant W_Identifier_Id :=
           +New_Identifier
           (Ada_Node => Expr,
            Domain   => Domain,
            Module   => Module,
            Symb   => NID (Name));

         --  Predicate used to define the aggregate/updated object

         Params_No_Ref : constant Transformation_Params :=
                           (File        => Params.File,
                            Phase       => Params.Phase,
                            Gen_Marker  => GM_None,
                            Ref_Allowed => False,
                            Old_Policy  => Ignore);

         --  Values used in calls to the aggregate function

         Ret_Type      : constant W_Type_Id := Type_Of_Node (Expr);

         --  Arrays of binders and arguments, and mapping of nodes to names

         Call_Params   : Binder_Array (1 .. Natural (Values.Length));
         Call_Args     : W_Expr_Array (1 .. Natural (Values.Length));
         Args_Map      : Ada_Ent_To_Why.Map;

         --  Additional arguments for the array bounds

         Bnd_Params    : Binder_Array
           (1 .. (if Needs_Bounds then 2 * Nb_Dim else 0));
         Bnd_Args      : W_Expr_Array
           (1 .. (if Needs_Bounds then 2 * Nb_Dim else 0));

         --  Counter and iterators

         Cnt           : Positive;
         Value         : Node_Lists.Cursor;
         Typ           : Node_Lists.Cursor;

         --  Variables for the call, guard and proposition for the axiom

         Aggr          : W_Expr_Id;
         Def_Pred      : W_Pred_Id;
         Guard_Conj    : W_Expr_Array (1 .. Natural (Values.Length));
         Guard         : W_Pred_Id;
         Axiom_Body    : W_Pred_Id := True_Pred;

         Aggr_Temp     : constant W_Identifier_Id :=
           New_Temp_Identifier (Typ => Ret_Type);

         --  Select files for the declaration and axiom

         Decl_File     : constant W_Section_Id := Dispatch_Entity (Expr);
         Compl_File    : constant W_Section_Id :=
           Dispatch_Entity_Completion (Expr);

         --  use this variable to temporarily store current theory
         Save_Theory   : W_Theory_Declaration_Id;

      --  Start of processing for Generate_Logic_Function

      begin
         --  Insert new modules for the logic function in the module map

         Insert_Extra_Module (Expr, Module);
         Insert_Extra_Module
           (Expr,
            New_Module (File => No_Symbol,
                        Name => Name & To_String (WNE_Axiom_Suffix)),
            Is_Axiom => True);

         --  Compute the parameters/arguments for the axiom/call as well as
         --  the guard (dynamic property of the aggregate values).
         --  As equality of array elements is done in the base type
         --  (to_rep (a [x]) = v), this guard is necessary for the axiom to be
         --  sound (if v is not in bounds, there is no a such that
         --  to_rep (a [x]) = v).

         Cnt   := 1;
         Value := Values.First;
         Typ := Types.First;
         while Value /= No_Element loop
            declare
               Ident    : constant W_Identifier_Id :=
                 New_Temp_Identifier
                   (Typ =>
                      (if Expr_Has_Relaxed_Init
                         (Element (Value), No_Eval => False)
                       then EW_Abstract (Element (Typ), Relaxed_Init => True)
                       else Type_Of_Node (Element (Typ))));
               B        : constant Binder_Type :=
                 (Ada_Node => Empty,
                  B_Name   => Ident,
                  B_Ent    => Null_Entity_Name,
                  Mutable  => False,
                  Labels   => <>);
               Dyn_Prop : constant W_Pred_Id :=
                 Compute_Dynamic_Invariant
                   (Expr   => +Ident,
                    Ty     => Element (Typ),
                    Params => Params);

            begin

               Call_Params (Cnt) := B;
               Call_Args (Cnt) := +Ident;
               Guard_Conj (Cnt) := +Dyn_Prop;

               --  Fill in mapping from Ada nodes to Why identifiers for the
               --  generation of the proposition in the defining axiom.

               Ada_Ent_To_Why.Insert
                 (Args_Map, Element (Value),
                  (Regular, Local => True, Init => <>, Main => B));

               Next (Typ);
               Next (Value);
               Cnt := Cnt + 1;
            end;
         end loop;

         Guard := +New_And_Expr (Guard_Conj, EW_Pred);

         --  Assume values of the aggregate's bounds. For delta aggregates,
         --  take the bounds of the array argument, otherwise, take the bounds
         --  of the type.

         if not Is_Static_Array_Type (Expr_Typ) then
            for Dim in 1 .. Nb_Dim loop
               declare
                  BT     : constant W_Type_Id := Nth_Index_Rep_Type_No_Bool
                    (Expr_Typ, Dim);
                  F_Expr  : constant W_Expr_Id :=
                    (if In_Delta_Aggregate then
                        Get_Array_Attr
                       (EW_Term, +Call_Args (1), Attribute_First, Dim)
                     else +New_Temp_Identifier (Typ => BT));
                  First_Eq : constant W_Pred_Id :=
                    +New_Comparison
                    (Symbol => Why_Eq,
                     Domain => EW_Pred,
                     Left   =>
                       +Get_Array_Attr
                       (EW_Term, +Aggr_Temp, Attribute_First, Dim),
                     Right  => F_Expr);
                  L_Expr  : constant W_Expr_Id :=
                    (if In_Delta_Aggregate then
                        Get_Array_Attr
                       (EW_Term, +Call_Args (1), Attribute_Last, Dim)
                     else +New_Temp_Identifier (Typ => BT));
                  Last_Eq : constant W_Pred_Id :=
                    +New_Comparison
                    (Symbol => Why_Eq,
                     Domain => EW_Pred,
                     Left   =>
                       +Get_Array_Attr
                       (EW_Term, +Aggr_Temp, Attribute_Last, Dim),
                     Right  => L_Expr);

               begin
                  --  Store the bounds in the arguments

                  if Needs_Bounds then
                     Bnd_Args (2 * Dim - 1) := F_Expr;
                     Bnd_Params (2 * Dim - 1) :=
                       (Ada_Node => Empty,
                        B_Name   => +F_Expr,
                        B_Ent    => Null_Entity_Name,
                        Mutable  => False,
                        Labels   => <>);
                     Bnd_Args (2 * Dim) := L_Expr;
                     Bnd_Params (2 * Dim) :=
                       (Ada_Node => Empty,
                        B_Name   => +L_Expr,
                        B_Ent    => Null_Entity_Name,
                        Mutable  => False,
                        Labels   => <>);
                  end if;

                  --  Add equalities to the axiom's body

                  Axiom_Body :=
                    +New_And_Then_Expr
                    (Domain => EW_Pred,
                     Left   => New_And_Expr (+First_Eq, +Last_Eq, EW_Pred),
                     Right  => +Axiom_Body);
               end;
            end loop;

            --  If bounds are taken from the type, we should add a guard to the
            --  axiom for the dynamic property of the array to avoid generating
            --  an unsound axiom if the bounds are not in their type.

            if Needs_Bounds then
               Axiom_Body :=
                 New_Conditional
                   (Condition   =>
                      +New_Dynamic_Property
                      (EW_Pred, Etype (Expr_Typ), Bnd_Args, Params_No_Ref),
                    Then_Part   => +Axiom_Body,
                    Typ         => EW_Bool_Type);
            end if;
         end if;

         --  Compute the call, guard and proposition for the axiom

         Axiom_Body :=
           +New_And_Then_Expr
           (Domain => EW_Pred,
            Left   => +Axiom_Body,
            Right  => +Transform_Array_Component_Associations
              (Expr   => Expr,
               Arr    => +Aggr_Temp,
               Args   => Args_Map,
               Params => Params_No_Ref));

         Aggr :=
           New_Call (Ada_Node => Expr,
                     Domain   => EW_Term,
                     Name     => Func,
                     Args     => Call_Args & Bnd_Args,
                     Typ      => Type_Of_Node (Etype (Expr)));

         --  Add guards for the dynamic_property of the value arguments of the
         --  aggregate.

         if not Is_True_Boolean (+Guard) then
            Axiom_Body :=
              New_Conditional
                (Condition   => +Guard,
                 Then_Part   => +Axiom_Body,
                 Typ         => EW_Bool_Type);
         end if;

         Def_Pred :=
           +New_Typed_Binding
             (Name   => Aggr_Temp,
              Domain => EW_Pred,
              Def    => Aggr,
              Context => +Axiom_Body);

         --  Generate the logic function declaration

         if Params.File = Decl_File then
            Save_Theory := Why_Sections (Decl_File).Cur_Theory;
            Why_Sections (Decl_File).Cur_Theory := Why_Empty;
         end if;

         Open_Theory
           (Decl_File, E_Module (Expr),
            Comment =>
              "Module for declaring an abstract function for the "
                & (if Nkind (Expr) = N_Delta_Aggregate
                   then "delta aggregate"
                   elsif In_Delta_Aggregate
                   then "update attribute"
                   else "aggregate")
                & " at "
                & (if Sloc (Expr) > 0 then
                      Build_Location_String (Sloc (Expr))
                   else "<no location>")
                & ", created in " & GNAT.Source_Info.Enclosing_Entity);

         Emit (Decl_File,
               New_Function_Decl (Domain      => EW_Pterm,
                                  Name        => To_Local (Func),
                                  Labels      => Symbol_Sets.Empty_Set,
                                  Location    => No_Location,
                                  Binders     => Call_Params & Bnd_Params,
                                  Return_Type => Ret_Type));

         Close_Theory (Decl_File,
                       Kind => Definition_Theory,
                       Defined_Entity => Expr);

         if Params.File = Decl_File then
            Why_Sections (Decl_File).Cur_Theory := Save_Theory;
         end if;

         --  Generate the axiom in a completion module

         if Params.File = Compl_File then
            Save_Theory := Why_Sections (Compl_File).Cur_Theory;
            Why_Sections (Compl_File).Cur_Theory := Why_Empty;
         end if;

         Open_Theory
           (Compl_File, E_Axiom_Module (Expr),
            Comment =>
              "Module for defining the value of the "
                & (if Nkind (Expr) = N_Delta_Aggregate
                   then "delta aggregate"
                   elsif In_Delta_Aggregate
                   then "update attribute"
                   else "aggregate")
                & " at "
                & (if Sloc (Expr) > 0 then
                      Build_Location_String (Sloc (Expr))
                   else "<no location>")
                & ", created in " & GNAT.Source_Info.Enclosing_Entity);
         Emit (Compl_File,
               New_Guarded_Axiom (Name     => NID (Def_Axiom),
                                  Binders  => Call_Params & Bnd_Params,
                                  Def      => Def_Pred));

         Close_Theory (Compl_File,
                       Kind => Axiom_Theory,
                       Defined_Entity => Expr);
         if Params.File = Compl_File then
            Why_Sections (Compl_File).Cur_Theory := Save_Theory;
         end if;
      end Generate_Logic_Function;

      ----------------------------
      -- Get_Aggregate_Elements --
      ----------------------------

      procedure Get_Aggregate_Elements
        (Expr         : Node_Id;
         Values       : out Node_Lists.List;
         Types        : out Node_Lists.List;
         Index_Values : out Node_Lists.List;
         Index_Types  : out Node_Lists.List)
      is
         Typ     : constant Entity_Id := Type_Of_Node (Etype (Etype (Expr)));
         --  We should use the aggregate's type Etype here for the checks as
         --  the aggregate's type may have incorrect index bounds.
         Num_Dim : constant Pos       := Number_Dimensions (Typ);

         -----------------------
         -- Local subprograms --
         -----------------------

         procedure Traverse_Value_At_Index
           (Dim                 : Pos;
            Index               : Node_Id;
            Expr_Or_Association : Node_Id);
         --  Traverse the value Expr_Or_Association to collect desired elements

         procedure Traverse_Rec_Aggregate
           (Dim   : Pos;
            Index : Node_Id;
            Expr  : Node_Id);
         --  Main recursive function operating over multi-dimensional array
         --  aggregates.

         -----------------------------
         -- Traverse_Value_At_Index --
         -----------------------------

         procedure Traverse_Value_At_Index
           (Dim                 : Pos;
            Index               : Node_Id;  --  Index type
            Expr_Or_Association : Node_Id)
         is
            Expr   : Node_Id;
            Choice : Node_Id;
            Rng    : Node_Id;

         begin
            --  If Expr_Or_Association is a component association, first we
            --  go through the component association and collect the
            --  choices to be used later for:
            --  * Index checks, in the case of normal aggregates.
            --  * Parameters to the logic function, in the case of delta
            --  aggregates.

            if Nkind (Expr_Or_Association) = N_Component_Association
              and then not Is_Others_Choice (Choices (Expr_Or_Association))
            then
               Index_Values.Append (Expr_Or_Association);
               Index_Types.Append (Etype (Index));

               --  For delta aggregates we also need the choices as
               --  parameters since they can be dynamic

               if In_Delta_Aggregate then

                  --  Collect the choices as parameters.
                  --  We cannot use Index_Values directly since they store
                  --  the whole associations. Instead, populate Values with
                  --  the parameters needed.

                  Choice := First (Choices (Expr_Or_Association));
                  while Present (Choice) loop
                     case Nkind (Choice) is
                        when N_Range =>

                           --  The high and low bounds of a range both
                           --  need to be parameters. We don't use the index
                           --  type for them as bounds can be outside of the
                           --  index sutype in case of empty ranges.

                           Rng := Get_Range (Choice);
                           Values.Append (Low_Bound (Rng));
                           Types.Append (Etype (Low_Bound (Rng)));
                           Values.Append (High_Bound (Rng));
                           Types.Append (Etype (High_Bound (Rng)));

                        when N_Aggregate =>

                           --  This is a special choice, the LHS of an
                           --  association of a 'Update of a
                           --  multi-dimensional array,
                           --  for example: (I, J, K) of
                           --  'Update((I, J, K) => New_Val)

                           pragma Assert
                             (Dim < Num_Dim and then Dim = 1
                                and then No (Component_Associations (Choice)));
                           declare
                              Multi_Exprs : constant List_Id :=
                                Expressions (Choice);
                              Multi_Expression : Node_Id :=
                                Nlists.First (Multi_Exprs);

                              Current_Index : Node_Id := Index;
                              --  Dim = 1 so Index is still first index here

                           begin
                              pragma Assert (List_Length (Multi_Exprs) =
                                               Num_Dim);

                              while Present (Multi_Expression) loop
                                 Values.Append (Multi_Expression);
                                 Types.Append (Etype (Current_Index));
                                 Next (Multi_Expression);
                                 Next_Index (Current_Index);
                              end loop;
                              pragma Assert (No (Current_Index));
                           end;

                        when others =>
                           Values.Append (Choice);
                           Types.Append (Etype (Index));
                     end case;
                     Next (Choice);
                  end loop;
               end if;
            end if;

            --  Next, for both positional and named associations, and for
            --  both normal and for delta aggregates, we fill the
            --  component expressions to the arrays Values and Types, to
            --  later be used as parameters.

            if Nkind (Expr_Or_Association) = N_Component_Association
              and then Box_Present (Expr_Or_Association)
            then
               null;
            else
               Expr :=
                 (if Nkind (Expr_Or_Association) =
                    N_Component_Association
                  then
                    Expression (Expr_Or_Association)
                  else
                    Expr_Or_Association);

               if Dim < Num_Dim and then not In_Delta_Aggregate then

                  --  Normal, multidimensional aggregate, for example:
                  --  Array_2D'(1      => (2 => Expr_1, others => Expr_2),
                  --            others => (others => Expr_3))
                  --
                  --  The components are aggregates as long as Dim < Num_Dim.
                  --  Keep recursively peeling the aggregates off.

                  pragma Assert (Nkind (Expr) = N_Aggregate);
                  Traverse_Rec_Aggregate (Dim + 1, Next_Index (Index), Expr);
               else

                  --  Two cases here:
                  --
                  --  1) A single dimensional aggregate, normal or delta,
                  --  (for example an innermost of a multidimensional
                  --  aggregate), or
                  --
                  --  2) A multidimensional 'Update aggregate of the form
                  --  'Update((I, J, K) => New_Val)
                  --
                  --  in both cases there are no more aggregates to peel off.

                  pragma Assert (Dim = Num_Dim or else
                                   (In_Delta_Aggregate and then Dim = 1));
                  declare
                     Exp_Type  : constant Node_Id := Component_Type (Typ);
                  begin

                     --  Collecting component expression for later use as
                     --  parameter.

                     Values.Append (Expr);
                     Types.Append (Exp_Type);
                  end;
               end if;
            end if;
         end Traverse_Value_At_Index;

         ----------------------------
         -- Traverse_Rec_Aggregate --
         ----------------------------

         procedure Traverse_Rec_Aggregate
           (Dim   : Pos;
            Index : Node_Id;
            Expr  : Node_Id)
         is
            Exprs       : constant List_Id :=
              (if Nkind (Expr) = N_Delta_Aggregate then No_List
               else Expressions (Expr));
            Assocs      : constant List_Id := Component_Associations (Expr);
            Expression  : Node_Id := Nlists.First (Exprs);
            Association : Node_Id := Nlists.First (Assocs);

         begin

            --  Positional association is not allowed in delta aggregate
            --  (except in an inner aggregate that is the choice in a
            --  component association of a multidimensional 'Update
            --  aggregate, but never on the outer level we are at here).

            pragma Assert (if Present (Expression) then
                             not In_Delta_Aggregate);

            while Present (Expression) loop
               Traverse_Value_At_Index (Dim, Index, Expression);
               Next (Expression);
            end loop;

            --  Although named association is not allowed after positional
            --  association, an "others" case is allowed, and this is included
            --  in the list of associations, so we always do the following.

            while Present (Association) loop
               Traverse_Value_At_Index (Dim, Index, Association);
               Next (Association);
            end loop;
         end Traverse_Rec_Aggregate;

      --  Start of processing for Get_Aggregate_Elements

      begin
         --  In the case of a delta aggregate, add the prefix to be
         --  a parameter to the logic function.

         if In_Delta_Aggregate then
            Values.Append (Update_Prefix);
            Types.Append (Etype (Update_Prefix));
         end if;

         Traverse_Rec_Aggregate (Dim   => 1,
                                 Index => First_Index (Typ),
                                 Expr  => Expr);
      end Get_Aggregate_Elements;

      -----------------------------
      -- Insert_Check_For_Ranges --
      -----------------------------

      procedure Insert_Check_For_Ranges (T : in out W_Expr_Id) is

         procedure Insert_Check_Rec (Expr : Node_Id; Dim : Positive);
         --  Introduce range checks for subtype indications in choices of an
         --  expression. Recursively call itself to checkchoices for upper
         --  dimensions in regular multidimensional aggregates.

         ----------------------
         -- Insert_Check_Rec --
         ----------------------

         procedure Insert_Check_Rec (Expr : Node_Id; Dim : Positive) is
            Assocs      : constant List_Id := Component_Associations (Expr);
            Association : Node_Id := Nlists.First (Assocs);
            Exprs       : constant List_Id :=
              (if Nkind (Expr) = N_Delta_Aggregate then No_List
               else Expressions (Expr));
            Expression  : Node_Id := Nlists.First (Exprs);

         begin
            --  Go over the list of association to check subtype indications
            --  in choices if any.

            while Present (Association) loop
               if not Is_Others_Choice (Choices (Association)) then
                  declare
                     Choice : Node_Id := First (Choices (Association));
                  begin
                     while Present (Choice) loop
                        case Nkind (Choice) is
                        when N_Subtype_Indication =>
                           T := +Sequence
                             (Ada_Node => Choice,
                              Left     => +Check_Scalar_Range
                                (Params => Params,
                                 N      => Get_Range (Choice),
                                 Base   => Entity (Subtype_Mark (Choice))),
                              Right    => +T);
                        when others =>
                           null;
                        end case;
                        Next (Choice);
                     end loop;
                  end;
               end if;

               --  In regular multidimensional aggregates, we also need to
               --  check subtype indication in expressions used for choices
               --  in upper dimensions.

               if not In_Delta_Aggregate and then Dim /= Nb_Dim then
                  Insert_Check_Rec
                    (SPARK_Atree.Expression (Association), Dim + 1);
               end if;
               Next (Association);
            end loop;

            --  In regular multidimensional aggregates, we may need to check
            --  subtype indication in expressions used for choices in upper
            --  dimensions.

            if not In_Delta_Aggregate and then Dim /= Nb_Dim then
               while Present (Expression) loop
                  Insert_Check_Rec (Expression, Dim + 1);
                  Next (Expression);
               end loop;
            end if;
         end Insert_Check_Rec;

      --  Start of processing of Insert_Check_For_Ranges

      begin
         Insert_Check_Rec (Expr, 1);
      end Insert_Check_For_Ranges;

      --------------------------------------------
      -- Transform_Array_Component_Associations --
      --------------------------------------------

      function Transform_Array_Component_Associations
        (Expr   : Node_Id;
         Arr    : W_Expr_Id;
         Args   : Ada_Ent_To_Why.Map;
         Params : Transformation_Params) return W_Pred_Id
      is
         Typ     : constant Entity_Id := Type_Of_Node (Expr);
         Num_Dim : constant Pos := Number_Dimensions (Typ);
         Ind_Arr : array (1 .. Num_Dim) of Node_Id;
         Binders : Binder_Array (1 .. Positive (Num_Dim));

         Indexes : W_Expr_Array (1 .. Positive (Num_Dim));
         --  This array contains either the identifiers for indexes in the
         --  normal translation, or the actual values of indexes in the
         --  translation for "simple" aggregates. For example, in the first
         --  case it could be:
         --     (tmp1, tmp2, tmp3)
         --  while in the second case it could be:
         --     (1, 3, 2)
         --  This allows using Constrain_Value_At_Index in both cases to get
         --  the value of the aggregate at the desired indexes.

         -----------------------
         -- Local subprograms --
         -----------------------

         type Transform_Rec_Func is not null access function
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id;
         --  Type of callback used to refer to either one of the recursive
         --  transformation functions for aggregate defined below, for use in
         --  Constrain_Value_At_Index.

         function Constrain_Value_At_Index
           (Dim                 : Pos;
            Expr_Or_Association : Node_Id;
            Callback            : Transform_Rec_Func) return W_Expr_Id;
         --  Return the proposition that the array at the given indices is
         --  equal to the value given in Expr_Or_Association, or else "true"
         --  for box association.

         function Is_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return Boolean;
         --  Detect whether aggregate Expr has no "others" or range choices, or
         --  multiple choices in an association.

         function Select_Nth_Index
           (Dim    : Pos;
            Offset : Nat) return W_Expr_Id;
         --  Return the value for Index at Offset from Id'First

         function Select_These_Choices
           (Dim : Pos;
            L   : List_Id) return W_Expr_Id;
         --  Return a proposition that expresses that Index satisfies one
         --  choice in the list of choices L. In the case of an aggregate of
         --  a delta aggregate, the (possibly dynamic) choices will be
         --  pulled from the arguments to the logic function.

         function Transform_Rec_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id;
         --  Main recursive function operating over multi-dimensional array
         --  aggregates.

         function Transform_Rec_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id;
         --  Specialized version of Transform_Rec_Aggregate when the aggregate
         --  is simple, as defined by Is_Simple_Aggregate.

         ------------------------------
         -- Constrain_Value_At_Index --
         ------------------------------

         function Constrain_Value_At_Index
           (Dim                 : Pos;
            Expr_Or_Association : Node_Id;
            Callback            : Transform_Rec_Func) return W_Expr_Id
         is
            --  Note that Expr_Or_Association here can be the updated
            --  expression in the default case of the logic function of a
            --  delta aggregate.
            Expr  : Node_Id;
            C_Typ : constant Entity_Id := Component_Type (Typ);

         begin
            if Nkind (Expr_Or_Association) = N_Component_Association
              and then Box_Present (Expr_Or_Association)
            then
               return +True_Pred;
            else
               Expr :=
                 (if Nkind (Expr_Or_Association) =
                    N_Component_Association
                  then
                     Expression (Expr_Or_Association)
                  else
                     Expr_Or_Association);

               if Dim < Num_Dim and then not In_Delta_Aggregate then
                  pragma Assert (Nkind (Expr) = N_Aggregate);
                  return Callback (Dim + 1, Expr);
                  pragma Annotate
                    (CodePeer, False_Positive, "validity check",
                     "false alarm on implicit result of callback");

               else
                  --  Whenever possible, take advantage of the why3 construct
                  --  for range constants.

                  if Is_Range_Type_In_Why (Etype (Expr))
                    and then Compile_Time_Known_Value (Expr)
                  then
                     return New_Comparison
                       (Symbol => Why_Eq,
                        Left   => New_Array_Access
                          (Ada_Node => Expr_Or_Association,
                           Domain   => EW_Term,
                           Ar       => Arr,
                           Index    => Indexes),
                        Right  =>
                          (if Has_Relaxed_Init (C_Typ) or else Init_Wrapper
                           then Insert_Simple_Conversion
                             (Ada_Node       => Empty,
                              Domain         => EW_Term,
                              Expr           => New_Range_Constant
                                (Value => Expr_Value (Expr),
                                 Typ   => EW_Abstract (C_Typ)),
                              To             =>
                                EW_Abstract (C_Typ, Relaxed_Init => True),
                              Force_No_Slide => True)
                           else New_Range_Constant
                             (Value => Expr_Value (Expr),
                              Typ   => EW_Abstract (C_Typ))),
                        Domain => EW_Pred);
                  end if;

                  --  For single dimensional aggregates (normal or
                  --  delta), and for multidimensional 'Update aggregates
                  --  there will be no more nested aggregates, so no
                  --  recursive callback, go ahead and create array
                  --  access and comparison.

                  declare
                     Binder  : constant Item_Type :=
                       Ada_Ent_To_Why.Element (Args, Expr);
                     Arg_Val : constant W_Expr_Id :=
                       (case Binder.Kind is
                           when Regular => +Binder.Main.B_Name,
                           when UCArray => +Binder.Content.B_Name,
                           when others  => raise Program_Error);
                     Is_Init : W_Pred_Id := True_Pred;
                     Value   : W_Expr_Id;
                     Read    : W_Expr_Id;

                  begin
                     Read := New_Array_Access (Ada_Node => Expr_Or_Association,
                                               Domain   => EW_Term,
                                               Ar       => Arr,
                                               Index    => Indexes);

                     --  Special case for the expression of the delta
                     --  aggregate. In that case, we want to build
                     --  the value Prefix(i,j..) with the default indexes.

                     if In_Delta_Aggregate and then Expr = Update_Prefix then
                        Value := New_Array_Access (Ada_Node => Empty,
                                                   Domain   => EW_Term,
                                                   Ar       => Arg_Val,
                                                   Index    => Indexes);

                     --  Use the split form of the component type for the
                     --  comparison to avoid introducing unnecessary
                     --  conversions whenever possible (see Type_Of_Node). This
                     --  is only correct because the axiom is guarded so that
                     --  Arg_Val is always in the appropriate type.

                     else
                        Value := Arg_Val;

                        --  If the value has a type which does not have
                        --  relaxed initialization, it must be initialized.

                        if (Has_Relaxed_Init (C_Typ) or else Init_Wrapper)
                          and then
                            (Has_Scalar_Type (C_Typ)
                             or else
                               not Is_Init_Wrapper_Type (Get_Type (Value)))
                        then
                           Is_Init := +Compute_Is_Initialized
                             (C_Typ, +Read, Params.Ref_Allowed, EW_Pred);
                        end if;

                        Read := Insert_Simple_Conversion
                          (Domain => EW_Term,
                           Expr   => Read,
                           To     => Get_Type (Value));
                     end if;

                     return New_And_Expr
                       (Left   => New_Comparison (Symbol => Why_Eq,
                                                  Left   => Read,
                                                  Right  => Value,
                                                  Domain => EW_Pred),
                        Right  => +Is_Init,
                        Domain => EW_Pred);
                  end;
               end if;
            end if;
         end Constrain_Value_At_Index;

         -------------------------
         -- Is_Simple_Aggregate --
         -------------------------

         function Is_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return Boolean
         is
            Exprs       : constant List_Id := Expressions (Expr);
            Assocs      : constant List_Id := Component_Associations (Expr);
            Association : Node_Id;
            Expression  : Node_Id;

            Is_Simple : Boolean := True;

            procedure Check_Simple (B : Boolean);
            --  Take into account the intermediate check B

            ------------------
            -- Check_Simple --
            ------------------

            procedure Check_Simple (B : Boolean) is
            begin
               Is_Simple := B and Is_Simple;
            end Check_Simple;

         begin
            Expression  := Nlists.First (Exprs);
            Association := Nlists.First (Assocs);

            while Present (Expression) loop
               --  For multi-dimensional aggregates, recurse

               if Dim < Num_Dim then
                  pragma Assert (Nkind (Expression) = N_Aggregate);
                  Check_Simple (Is_Simple_Aggregate (Dim + 1, Expression));
               end if;
               Next (Expression);
            end loop;

            while Present (Association) loop

               --  Check that there is only one choice, and it is neither a
               --  range not a dynamic value.

               declare
                  Only_Choice : constant Node_Id :=
                                  First (Choices (Association));
               begin
                  Check_Simple
                    (List_Length (Choices (Association)) = 1
                      and then not Discrete_Choice_Is_Range (Only_Choice)
                      and then Compile_Time_Known_Value (Only_Choice));
               end;

               --  For multi-dimensional aggregates, recurse

               Expression := SPARK_Atree.Expression (Association);

               if Dim < Num_Dim then
                  pragma Assert (Nkind (Expression) = N_Aggregate);
                  Check_Simple (Is_Simple_Aggregate (Dim + 1, Expression));
               end if;

               Next (Association);
            end loop;

            return Is_Simple;
         end Is_Simple_Aggregate;

         ----------------------
         -- Select_Nth_Index --
         ----------------------

         function Select_Nth_Index
           (Dim    : Pos;
            Offset : Nat) return W_Expr_Id
         is
            Rng        : constant Node_Id := Get_Range (Ind_Arr (Dim));
            Typ        : constant W_Type_Id := Base_Why_Type_No_Bool
              (Etype (Rng));
            Low        : constant Node_Id := Low_Bound (Rng);
            First, Val : W_Expr_Id;

         begin

            if Is_Static_Expression (Low) then
               Val :=
                 New_Discrete_Constant
                   (Value => Expr_Value (Low) + UI_From_Int (Offset),
                    Typ   => Typ);
            else
               First := New_Attribute_Expr (Etype (Rng),
                                            EW_Term,
                                            Attribute_First,
                                            Params);

               Val :=
                 New_Discrete_Add (Domain => Domain,
                                   Left   => First,
                                   Right  => New_Discrete_Constant
                                     (Value => UI_From_Int (Offset),
                                      Typ   => Typ));
            end if;

            return Val;
         end Select_Nth_Index;

         --------------------------
         -- Select_These_Choices --
         --------------------------

         function Select_These_Choices
           (Dim : Pos;
            L   : List_Id) return W_Expr_Id
         is
            Result     : W_Expr_Id := +False_Pred;
            Choice     : Node_Id := First (L);
            Rng_Expr   : W_Expr_Id;
            Arg_Choice : W_Expr_Id;
         begin
            while Present (Choice) loop
               if In_Delta_Aggregate then
                  case Nkind (Choice) is
                     when N_Range =>
                        declare
                           Low  : constant Node_Id :=
                             Low_Bound (Get_Range (Choice));
                           High : constant Node_Id :=
                             High_Bound (Get_Range (Choice));
                           Arg_Low  : W_Expr_Id;
                           Arg_High : W_Expr_Id;
                        begin
                           Arg_Low :=
                             +Ada_Ent_To_Why.Element (Args, Low).Main.B_Name;
                           Arg_Low :=
                             Insert_Simple_Conversion (Domain => EW_Term,
                                                       Expr   => Arg_Low,
                                                       To     =>
                                                         Base_Why_Type_No_Bool
                                                         (Arg_Low));

                           Arg_High :=
                             +Ada_Ent_To_Why.Element (Args, High).Main.B_Name;

                           Arg_High :=
                             Insert_Simple_Conversion (Domain => EW_Term,
                                                       Expr   => Arg_High,
                                                       To     =>
                                                         Base_Why_Type_No_Bool
                                                        (Arg_High));
                           Rng_Expr :=
                             New_Range_Expr (Domain => EW_Pred,
                                             Low    => Arg_Low,
                                             High   => Arg_High,
                                             Expr   => Indexes (Integer (Dim))
                                            );
                        end;

                     when N_Aggregate =>
                        pragma Assert (Dim < Num_Dim and then Dim = 1);

                        --  This is a choice of a multidimensional 'Update,
                        --  for example (I, J, K) of
                        --  'Update((I, J, K) => New_Val).
                        --  Create a conjunction of comparisons, one for
                        --  each dimension.

                        declare
                           Conjunct     : W_Expr_Id := +True_Pred;
                           Arg_Index    : W_Expr_Id;
                           Multi_Exprs : constant List_Id :=
                             Expressions (Choice);
                           Multi_Assocs : constant List_Id :=
                             Component_Associations (Choice);
                           Multi_Expression : Node_Id :=
                             Nlists.First (Multi_Exprs);

                           --  Start with first dimension, Dim = 1 always
                           --  here.

                           Current_Dim  : Positive := 1;
                        begin
                           pragma Assert (No (Multi_Assocs)
                              and then List_Length (Multi_Exprs) = Num_Dim);

                           while Present (Multi_Expression) loop
                              Arg_Index :=
                                +Ada_Ent_To_Why.Element
                                (Args, Multi_Expression).Main.B_Name;
                              Arg_Index :=
                                Insert_Simple_Conversion
                                (Domain => EW_Term,
                                 Expr   => Arg_Index,
                                 To     => Base_Why_Type_No_Bool
                                   (Get_Type (Arg_Index)));
                              Rng_Expr :=
                                New_Comparison
                                (Symbol => Why_Eq,
                                 Left   => Indexes (Integer (Current_Dim)),
                                 Right  => Arg_Index,
                                 Domain => EW_Pred);
                              Conjunct := New_And_Expr (Left   => Conjunct,
                                                        Right  => Rng_Expr,
                                                        Domain => EW_Pred);
                              Next (Multi_Expression);
                              Current_Dim := Current_Dim + 1;
                           end loop;

                           pragma Assert (Pos (Current_Dim - 1) = Num_Dim);

                           Rng_Expr := Conjunct;
                        end;

                     when others =>
                        Arg_Choice :=
                          +Ada_Ent_To_Why.Element (Args, Choice).Main.B_Name;
                        Arg_Choice :=
                          Insert_Simple_Conversion (Domain => EW_Term,
                                                    Expr   => Arg_Choice,
                                                    To     =>
                                                       Base_Why_Type_No_Bool
                                                      (Get_Type (Arg_Choice)));

                        Rng_Expr :=
                          New_Comparison (Symbol => Why_Eq,
                                          Left   => Indexes (Integer (Dim)),
                                          Right  => Arg_Choice,
                                          Domain => EW_Pred);
                  end case;
               else
                  --  The choices are not arguments, proceed with standard
                  --  transformation of discrete choice
                  Rng_Expr :=
                    Transform_Discrete_Choice
                      (Choice      => Choice,
                       Choice_Type => Empty,
                       Expr        => Indexes (Integer (Dim)),
                       Domain      => EW_Pred,
                       Params      => Params);
               end if;

               Result := New_Or_Expr (Left   => Result,
                                      Right  => Rng_Expr,
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
            Callback : constant Transform_Rec_Func :=
                         Transform_Rec_Aggregate'Access;
            Exprs    : constant List_Id :=
              (if Nkind (Expr) = N_Delta_Aggregate then No_List
               else Expressions (Expr));
            Assocs   : constant List_Id := Component_Associations (Expr);

            Association : Node_Id;
            Expression  : Node_Id;
            Else_Part   : W_Expr_Id := +True_Pred;
            Assocs_Len  : Nat;

         begin
            Assocs_Len := List_Length (Assocs);
            --  Starting with last association
            Association :=
              (if Nlists.Is_Empty_List (Assocs) then Empty
               else Nlists.Last (Assocs));

            --  First, generate else part:
            if Present (Association) then
               if In_Delta_Aggregate then

                  --  Setting up for delta transformation/axiom generation...

                  --  For delta aggregates we always want a default value in
                  --  the logic function so populate the else part properly.
                  --  Send the Prefix in to use for default value in the
                  --  logic function.
                  Else_Part :=
                    Constrain_Value_At_Index (Dim, Update_Prefix, Callback);

                  --  Next, constructing else part for a "normal" aggregate,
                  --  special case for "others" choice...
               elsif (List_Length (Choices (Association)) = 1
                        and then
                        --  Case of "others" choice
                        Nkind (First (Choices (Association))) =
                        N_Others_Choice)
                 or else
                 --  Case of a single association
                 Assocs_Len = 1
               then
                  --  Special case for "others" choice, which must
                  --  appear alone as last association. This case also
                  --  deals with a single association, wich may be
                  --  useful when an "others" dynamic range is
                  --  represented using X'Range or X'First..X'Last or
                  --  X, which should not be translated as
                  --  such. Indeed, these reference variable X which
                  --  is not known in the context of the proposition
                  --  generated here.
                  if not Box_Present (Association) then
                     Else_Part :=
                       Constrain_Value_At_Index (Dim, Association, Callback);
                  end if;
                  --  Dropping this single (and thus last) element.
                  Prev (Association);
                  Assocs_Len := Assocs_Len - 1;
               else
                  --  Default else part for a normal aggregate
                  Else_Part := +True_Pred;
               end if;
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
                        Condition =>
                          +New_Comparison
                            (Symbol    => Why_Eq,
                             Left      => Indexes (Integer (Dim)),
                             Right     => Select_Nth_Index (Dim, Offset),
                             Domain    => EW_Pred),
                        Then_Part =>
                          Constrain_Value_At_Index
                            (Dim, Expression, Callback));
                     Prev (Expression);
                  end loop;

                  return New_Conditional
                    (Domain      => EW_Pred,
                     Condition   =>
                       +New_Comparison
                         (Symbol    => Why_Eq,
                          Left      => Indexes (Integer (Dim)),
                          Right     => Select_Nth_Index (Dim, 0),
                          Domain    => EW_Pred),
                     Then_Part   =>
                       Constrain_Value_At_Index (Dim, Expression, Callback),
                     Elsif_Parts => Elsif_Parts,
                     Else_Part   => Else_Part);
               end;

            elsif Present (Association) then
               --  This either empty, or still at the last association
               --  (second from last if we have chopped off an others)

               declare
                  Condition   : W_Expr_Id;
                  Then_Part   : W_Expr_Id;
                  Elsif_Parts : W_Expr_Array (1 .. Integer (Assocs_Len) - 1);
               begin
                  --  The conditional in the logic function axiom must be
                  --  generated in the reverse order of the associations
                  --  for delta semantics which allows duplicate choices.
                  --  For a normal aggregate this order does not matter since
                  --  they cannot have overlapping choices. So we share this
                  --  implementation.
                  --
                  --  Generate If condition and Then part:
                  --
                  --  The first condition (if) in the axiom corresponds to
                  --  the last association:
                  Condition := +Select_These_Choices (Dim,
                                                      Choices (Association));
                  Then_Part := Constrain_Value_At_Index (Dim,
                                                         Association,
                                                         Callback);
                  Prev (Association);
                  if Present (Association) then
                     --  If we have any more associations they go into
                     --  the elsif branches, in reverse order:

                     for Offset in reverse 1 .. Assocs_Len - 1 loop
                        --  Loop to generate Elsif Then parts.

                        --  Store in reverse order here (Assocs_Len - Offset)
                        Elsif_Parts (Integer (Assocs_Len - Offset)) :=
                          New_Elsif
                          (Domain    => EW_Pred,
                           Condition =>
                             +Select_These_Choices
                               (Dim, Choices (Association)),
                           Then_Part =>
                             Constrain_Value_At_Index
                             (Dim, Association, Callback));
                        Prev (Association);
                     end loop;
                  end if;

                  --  Finally, generate the whole ITE
                  return
                    New_Conditional (Domain      => EW_Pred,
                                     Condition   => Condition,
                                     Then_Part   => Then_Part,
                                     Elsif_Parts => Elsif_Parts,
                                     Else_Part   => Else_Part);
               end;
            else
               return Else_Part;
            end if;
         end Transform_Rec_Aggregate;

         ------------------------------------
         -- Transform_Rec_Simple_Aggregate --
         ------------------------------------

         function Transform_Rec_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id
         is
            Callback    : constant Transform_Rec_Func :=
                            Transform_Rec_Simple_Aggregate'Access;
            Exprs       : constant List_Id := Expressions (Expr);
            Assocs      : constant List_Id := Component_Associations (Expr);
            Association : Node_Id;
            Expression  : Node_Id;

         begin
            Expression  := Nlists.First (Exprs);
            Association := Nlists.First (Assocs);

            if Present (Expression) then
               pragma Assert (No (Association));

               declare
                  Conjuncts : W_Expr_Array
                    (1 .. Integer (List_Length (Exprs)));
               begin
                  for Offset in 1 .. List_Length (Exprs) loop
                     Indexes (Integer (Dim)) :=
                       Select_Nth_Index (Dim, Offset - 1);
                     Conjuncts (Integer (Offset)) :=
                       Constrain_Value_At_Index (Dim, Expression, Callback);
                     Next (Expression);
                  end loop;

                  return New_And_Expr (Domain    => EW_Pred,
                                       Conjuncts => Conjuncts);
               end;

            else
               pragma Assert (Present (Association));

               declare
                  Conjuncts : W_Expr_Array
                    (1 .. Integer (List_Length (Assocs)));
               begin
                  for Offset in 1 .. List_Length (Assocs) loop
                     pragma Assert (List_Length (Choices (Association)) = 1);
                     Indexes (Integer (Dim)) :=
                       Transform_Expr (Expr          =>
                                         First (Choices (Association)),
                                       Expected_Type => Base_Why_Type_No_Bool
                                       (Etype (First (Choices (Association)))),
                                       Domain        => EW_Term,
                                       Params        => Params);
                     Conjuncts (Integer (Offset)) :=
                       Constrain_Value_At_Index (Dim, Association, Callback);
                     Next (Association);
                  end loop;

                  return New_And_Expr (Domain    => EW_Pred,
                                       Conjuncts => Conjuncts);
               end;
            end if;
         end Transform_Rec_Simple_Aggregate;

      --  Start of processing for Transform_Array_Component_Associations

      begin
         --  Fill the array of index nodes

         Ind_Arr (1) := First_Index (Typ);
         for Dim in 2 .. Num_Dim loop
            Ind_Arr (Dim) := Next_Index (Ind_Arr (Dim - 1));
         end loop;

         --  Define index variables

         for J in 1 .. Integer (Num_Dim) loop
            Binders (J) :=
              (B_Name => New_Temp_Identifier
                 (Typ => Nth_Index_Rep_Type_No_Bool (E   => Typ,
                                                     Dim => J)),
               B_Ent  => Null_Entity_Name,
               others => <>);
            Indexes (J) := +Binders (J).B_Name;
         end loop;

         --  Create the proposition defining the aggregate

         if not In_Delta_Aggregate
           and then Is_Simple_Aggregate (Dim => 1, Expr => Expr)
         then
            return +Transform_Rec_Simple_Aggregate (Dim => 1, Expr => Expr);
         else
            return New_Universal_Quantif
              (Binders => Binders,
               Pred    =>
                 +Transform_Rec_Aggregate
                 (Dim => 1, Expr => Expr));
         end if;
      end Transform_Array_Component_Associations;

      --  Elements of the aggregate

      Values       : Node_Lists.List;
      Types        : Node_Lists.List;
      Index_Values : Node_Lists.List;
      Index_Types  : Node_Lists.List;

   --  Start of processing for Transform_Aggregate

   begin
      --  Get the aggregate elements that should be passed in parameter

      Get_Aggregate_Elements
        (Expr, Values, Types, Index_Values, Index_Types);

      --  If not done already, generate the logic function

      declare
         M : W_Module_Id := E_Module (Expr);
      begin
         if M = Why_Empty then
            Generate_Logic_Function (Expr, Values, Types);
            M := E_Module (Expr);
         end if;
         return
           Complete_Translation
             (Params,
              Domain,
              New_Identifier
                (Ada_Node => Expr,
                 Domain   => Domain,
                 Module   => M,
                 Symb     => NID (Lower_Case_First (Img (Get_Name (M))))),
              Values,
              Types,
              Index_Values,
              Index_Types);
      end;
   end Transform_Aggregate;

   --------------------------------
   -- Transform_Array_Comparison --
   --------------------------------

   function Transform_Array_Comparison
     (Op       : N_Op_Compare;
      Left     : W_Expr_Id;
      Right    : W_Expr_Id;
      Domain   : EW_Domain;
      Ada_Node : Node_Id) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 6);
      T         : W_Expr_Id;

      --  Check that operands are initialized

      Left_Type  : constant Entity_Id := Etype (Left_Opnd (Ada_Node));
      Left_Expr  : constant W_Expr_Id := New_Temp_For_Expr
        (Insert_Initialization_Check
           (Left_Opnd (Ada_Node), Left_Type, Left, Domain));
      Right_Expr : constant W_Expr_Id := New_Temp_For_Expr
        (Insert_Initialization_Check
           (Right_Opnd (Ada_Node), Left_Type, Right, Domain));
      Arg_Ind    : Positive := 1;
   begin
      Add_Array_Arg (Subdomain, Args, Left_Expr, Arg_Ind);
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);

      --  Add conversions from wrapper types if needed. Initialization checks
      --  are inserted earlier.

      if Is_Init_Wrapper_Type (Get_Type (Left_Expr)) then
         Args (1) := New_Call
           (Ada_Node => Ada_Node,
            Domain   => Subdomain,
            Name     => Get_Array_Of_Wrapper_Name (Left_Type),
            Args     => (1 => Args (1)),
            Typ      => EW_Split (Left_Type));
      end if;
      if Is_Init_Wrapper_Type (Get_Type (Right_Expr)) then
         Args (4) := New_Call
           (Ada_Node => Ada_Node,
            Domain   => Subdomain,
            Name     => Get_Array_Of_Wrapper_Name (Left_Type),
            Args     => (1 => Args (4)),
            Typ      => EW_Split (Left_Type));
      end if;

      T :=
        New_Call
          (Ada_Node => Ada_Node,
           Domain   => Subdomain,
           Name     => Get_Array_Theory_1_Comp (Left_Type).Compare,
           Args     => Args,
           Typ      => EW_Int_Type);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Left_Expr,
                             Context => T);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
                             Context => T);
      T := New_Comparison
        (Symbol    => Transform_Compare_Op (Op, EW_Int_Type, Domain),
         Left      => T,
         Right     =>
           New_Integer_Constant (Value  => Uint_0),
         Domain    => Domain);
      return T;
   end Transform_Array_Comparison;

   ------------------------------
   -- Transform_Array_Equality --
   ------------------------------

   function Transform_Array_Equality
     (Op        : N_Op_Compare;
      Left      : W_Expr_Id;
      Right     : W_Expr_Id;
      Left_Type : Entity_Id;
      Domain    : EW_Domain;
      Ada_Node  : Node_Id) return W_Expr_Id
   is
      Dim       : constant Positive :=
        Positive (Number_Dimensions (Retysp (Left_Type)));
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 4 * Dim + 2);
      T         : W_Expr_Id;

      --  Check that operands are initialized

      Left_Expr  : constant W_Expr_Id := New_Temp_For_Expr
        (Insert_Initialization_Check
           (Left_Opnd (Ada_Node), Left_Type, Left, Domain));
      Right_Expr : constant W_Expr_Id := New_Temp_For_Expr
        (Insert_Initialization_Check
           (Right_Opnd (Ada_Node), Left_Type, Right, Domain));
      Arg_Ind    : Positive := 1;
   begin
      Add_Array_Arg (Subdomain, Args, Left_Expr, Arg_Ind);
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);

      --  Add conversions from wrapper types if needed. Initialization checks
      --  are inserted earlier.

      if Is_Init_Wrapper_Type (Get_Type (Left_Expr)) then
         Args (1) := New_Call
           (Ada_Node => Ada_Node,
            Domain   => Subdomain,
            Name     => Get_Array_Of_Wrapper_Name (Left_Type),
            Args     => (1 => Args (1)),
            Typ      => EW_Split (Left_Type));
      end if;
      if Is_Init_Wrapper_Type (Get_Type (Right_Expr)) then
         Args (2 + 2 * Dim) := New_Call
           (Ada_Node => Ada_Node,
            Domain   => Subdomain,
            Name     => Get_Array_Of_Wrapper_Name (Left_Type),
            Args     => (1 => Args (2 + 2 * Dim)),
            Typ      => EW_Split (Left_Type));
      end if;

      T :=
        New_Call
          (Ada_Node => Ada_Node,
           Domain   => Subdomain,
           Name     =>
             Get_Array_Theory (Etype (Left_Opnd (Ada_Node))).Bool_Eq,
           Args     => Args,
           Typ      => EW_Bool_Type);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Left_Expr,
                             Context => T);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
                             Context => T);
      if Domain = EW_Pred then
         T := New_Comparison
           (Symbol    => Transform_Compare_Op (Op, EW_Bool_Type, Domain),
            Left      => T,
            Right     => New_Literal (Domain => Subdomain,
                                      Value  => EW_True),
            Domain    => Domain);
      elsif Op = N_Op_Ne then
         T :=
           New_Call (Domain => Domain,
                     Name   => M_Boolean.Notb,
                     Args   => (1 => T),
                     Typ    => EW_Bool_Type);
      end if;
      return T;
   end Transform_Array_Equality;

   --------------------------------
   -- Transform_Array_Logical_Op --
   --------------------------------

   function Transform_Array_Logical_Op
     (Op        : N_Binary_Op;
      Left      : W_Expr_Id;
      Right     : W_Expr_Id;
      Left_Type : Entity_Id;
      Domain    : EW_Domain;
      Ada_Node  : Node_Id;
      Do_Check  : Boolean) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 6);
      T         : W_Expr_Id;
      Arg_Ind   : Positive := 1;

      --  Insert initialization checks for operands

      Left_Expr : constant W_Expr_Id := New_Temp_For_Expr
        (Insert_Initialization_Check
           (Left_Opnd (Ada_Node), Left_Type, Left, Domain));
      Right_Expr : constant W_Expr_Id := New_Temp_For_Expr
        (Insert_Initialization_Check
           (Right_Opnd (Ada_Node), Left_Type, Right, Domain));
      Array_Theory : constant M_Array_1_Bool_Op_Type :=
        Get_Array_Theory_1_Bool_Op (Etype (Left_Opnd (Ada_Node)));
      W_Op      : constant W_Identifier_Id :=
        (case Op is
            when N_Op_And => Array_Theory.Andb,
            when N_Op_Or  => Array_Theory.Orb,
            when N_Op_Xor => Array_Theory.Xorb,
            when others   => raise Program_Error);

      Left_Length  : constant W_Expr_Id :=
        Build_Length_Expr (Domain => EW_Term, Expr => Left_Expr, Dim => 1);
      Length_Check : constant W_Expr_Id :=
        +New_Length_Equality (Left_Arr  => Left_Expr,
                              Right_Arr => Right_Expr,
                              Dim       => 1);

      Index_Type : constant W_Type_Id :=
        (if First_Index (Retysp (Left_Type)) = Empty
         then EW_Int_Type
         else Base_Why_Type_No_Bool (First_Index (Retysp (Left_Type))));

      --  if Length (Left) > 0 then not (Left'First = Left'Last and
      --                                 Left'Last  = 1);
      Range_Check  : constant W_Expr_Id :=
        New_Conditional
          (Domain    => EW_Pred,
           Condition =>
             New_Call
               (Domain => EW_Pred,
                Typ    => EW_Bool_Type,
                Name   => Int_Infix_Gt,
                Args   => (+Left_Length,
                           New_Integer_Constant (Value => Uint_0))),
           Then_Part =>
             New_Not
               (Domain   => EW_Pred,
                Right    =>
                  New_And_Expr
                    (Left   =>
                           New_Call
                       (Domain => EW_Pred,
                        Typ    => EW_Bool_Type,
                        Name   => Why_Eq,
                        Args   =>
                          (1 =>
                               +E_Symb (Component_Type (Retysp (Left_Type)),
                                        WNE_Attr_First),
                           2 =>
                               +E_Symb (Component_Type (Retysp (Left_Type)),
                                        WNE_Attr_Last))),
                     Right  =>
                       New_Call
                         (Domain => EW_Pred,
                          Name   => Why_Eq,
                          Typ    => EW_Bool_Type,
                          Args   =>
                            (1 => New_Discrete_Constant (Value => Uint_1,
                                                         Typ   => Index_Type),
                             2 =>
                               +E_Symb (Component_Type (Retysp (Left_Type)),
                                        WNE_Attr_Last))),
                     Domain => EW_Pred)));
   begin
      Add_Array_Arg (Subdomain, Args, Left_Expr, Arg_Ind);
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);

      --  Add conversions from wrapper types if needed. Initialization checks
      --  are inserted earlier.

      if Is_Init_Wrapper_Type (Get_Type (Left_Expr)) then
         Args (1) := New_Call
           (Ada_Node => Ada_Node,
            Domain   => Subdomain,
            Name     => Get_Array_Of_Wrapper_Name (Left_Type),
            Args     => (1 => Args (1)),
            Typ      => EW_Split (Left_Type));
      end if;
      if Is_Init_Wrapper_Type (Get_Type (Right_Expr)) then
         Args (4) := New_Call
           (Ada_Node => Ada_Node,
            Domain   => Subdomain,
            Name     => Get_Array_Of_Wrapper_Name (Left_Type),
            Args     => (1 => Args (4)),
            Typ      => EW_Split (Left_Type));
      end if;

      --  Call to operator

      T :=
        New_Call
          (Ada_Node => Ada_Node,
           Domain   => Subdomain,
           Name     => W_Op,
           Args     => Args,
           Typ      => Type_Of_Node (Left_Type));

      if Do_Check then

         --  Length check, Left and Right should have the same length

         T := +Sequence (New_Ignore (Prog =>
               New_Located_Assert (Ada_Node,
                                   +Length_Check,
                                   VC_Length_Check,
                                   EW_Assert)),
                         +T);

         --  Range check : for all I, Left (I) Op Right (I) should be in range.
         --  The only way to generate an element not in range using a binary
         --  operator is to call xor on arrays of the singleton subtype True of
         --  boolean.

         if not Is_Standard_Boolean_Type (Component_Type (Retysp (Left_Type)))
           and then W_Op = Array_Theory.Xorb
         then
            T := +Sequence (New_Ignore (Prog =>
                                          New_Located_Assert (Ada_Node,
                                            +Range_Check,
                                            VC_Range_Check,
                                            EW_Assert)),
                            +T);
         end if;
      end if;

      --  Conversion from base, first and right are attributes of left

      if not Has_Static_Array_Type (Left_Type) then
         T := Array_Convert_From_Base
           (Domain => Subdomain,
            Ty     => Left_Type,
            Ar     => T,
            First  =>
              Get_Array_Attr (Domain => Subdomain,
                              Expr   => Left_Expr,
                              Attr   => Attribute_First,
                              Dim    => 1),
            Last   =>
              Get_Array_Attr (Domain => Subdomain,
                              Expr   => Left_Expr,
                              Attr   => Attribute_Last,
                              Dim    => 1));
      end if;

      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Left_Expr,
                             Context => T);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
                             Context => T);
      return T;
   end Transform_Array_Logical_Op;

   ------------------------------
   -- Transform_Array_Negation --
   ------------------------------

   function Transform_Array_Negation
     (Right      : W_Expr_Id;
      Right_Type : Entity_Id;
      Domain     : EW_Domain;
      Ada_Node   : Node_Id;
      Do_Check   : Boolean) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 3);
      T         : W_Expr_Id;
      Arg_Ind   : Positive := 1;

      --  Insert initialization checks for operand

      Right_Expr : constant W_Expr_Id := New_Temp_For_Expr
        (Insert_Initialization_Check
           (Right_Opnd (Ada_Node), Right_Type, Right, Domain));

      Right_Length : constant W_Expr_Id :=
        Build_Length_Expr (Domain => EW_Term, Expr => Right_Expr, Dim => 1);
      Range_Check  : constant W_Expr_Id :=
        New_Conditional
          (Domain    => EW_Pred,
           Condition =>
             New_Call
               (Domain => EW_Pred,
                Typ    => EW_Bool_Type,
                Name   => Int_Infix_Gt,
                Args   => (1 => +Right_Length,
                           2 => New_Integer_Constant (Value => Uint_0))),
           Then_Part =>
             New_Call
               (Domain => EW_Pred,
                Name   => Int_Infix_Lt,
                Typ    => EW_Bool_Type,
                Args   =>
                  (1 => +E_Symb (Component_Type (Right_Type), WNE_Attr_First),
                   2 =>
                     +E_Symb (Component_Type (Right_Type), WNE_Attr_Last))));
   begin
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);

      --  Add conversions from wrapper types if needed. Initialization checks
      --  are inserted earlier.

      if Is_Init_Wrapper_Type (Get_Type (Right_Expr)) then
         Args (1) := New_Call
           (Ada_Node => Ada_Node,
            Domain   => Subdomain,
            Name     => Get_Array_Of_Wrapper_Name (Right_Type),
            Args     => (1 => Args (1)),
            Typ      => EW_Split (Right_Type));
      end if;

      --  Call to operator

      T :=
        New_Call
          (Ada_Node => Ada_Node,
           Domain   => Subdomain,
           Name     => Get_Array_Theory_1_Bool_Op (Etype (Ada_Node)).Notb,
           Args     => Args,
           Typ      => Type_Of_Node (Right_Type));

      if Do_Check then

         --  Range check : for all I, Not Right (I) should be in range.
         --  The only way to generate an element not in range using negation
         --  is to call it on an array of a singleton subtype of boolean.

         if not Is_Standard_Boolean_Type (Component_Type (Right_Type)) then
            T := +Sequence (New_Ignore (Prog =>
                                          New_Located_Assert (Ada_Node,
                                            +Range_Check,
                                            VC_Range_Check,
                                            EW_Assert)),
                            +T);
         end if;
      end if;

      --  Conversion from base

      if not Has_Static_Array_Type (Right_Type) then
         T := Array_Convert_From_Base
           (Domain => Subdomain,
            Ty     => Right_Type,
            Ar     => T,
            First  =>
              Get_Array_Attr (Domain => Subdomain,
                              Expr   => Right_Expr,
                              Attr   => Attribute_First,
                              Dim    => 1),
            Last   =>
              Get_Array_Attr (Domain => Subdomain,
                              Expr   => Right_Expr,
                              Attr   => Attribute_Last,
                              Dim    => 1));
      end if;

      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
                             Context => T);
      return T;
   end Transform_Array_Negation;

   ------------------------------------
   -- Transform_Assignment_Statement --
   ------------------------------------

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id is
      Lvalue     : constant Node_Id := SPARK_Atree.Name (Stmt);
      Typ        : constant Entity_Id := Retysp (Etype (Lvalue));
      L_Type     : constant W_Type_Id :=
        (if Expr_Has_Relaxed_Init (Lvalue)
         and then not Is_Scalar_Type (Etype (Lvalue))
         then EW_Init_Wrapper (Type_Of_Node (Etype (Lvalue)))
         else Type_Of_Node (Etype (Lvalue)));
      --  We go to the wrapper type if lvalue has relaxed initialization
      --  except for scalar types for which a copy is a read.

      T          : W_Prog_Id :=
        +Transform_Expr (Expression (Stmt),
                         L_Type,
                         EW_Prog,
                         Params => Body_Params);
      Lgth_Check : constant Boolean :=
        Present (Get_Ada_Node (+L_Type)) and then

        --  Length check needed for assignment into a non-static array type

        (Is_Array_Type (Get_Ada_Node (+L_Type)) and then
           not Is_Static_Array_Type (Get_Ada_Node (+L_Type)));

         --  Discriminant check needed for assignment into a non-constrained
         --  record type. Constrained record type are handled by the
         --  conversion.

      Disc_Check : constant Boolean :=
        Present (Get_Ada_Node (+L_Type)) and then
        (if Is_Access_Type (Get_Ada_Node (+L_Type)) then
            Count_Discriminants
           (Directly_Designated_Type
                (Get_Ada_Node (+L_Type))) > 0
         and then not Is_Constrained (Directly_Designated_Type
                                      (Get_Ada_Node (+L_Type)))

         else
            Count_Discriminants (Get_Ada_Node (+L_Type)) > 0
         and then not Is_Constrained (Get_Ada_Node (+L_Type)));

      Tmp      : constant W_Expr_Id :=
        New_Temp_For_Expr (+T, Lgth_Check or else Disc_Check);

   begin
      --  The Exp_Entity type is in fact the type that is expected in Why.
      --  The L_Type is a more precise type entity in Ada. We have to
      --  respect both constraints here, so we first convert to the Ada type
      --  (to get checks), and then convert to Why (without checks) to get the
      --  types right.

      if Lgth_Check then
         declare
            Lval  : constant W_Expr_Id :=
              New_Temp_For_Expr
                (Transform_Expr (Lvalue, EW_Prog, Body_Params), True);
            Dim   : constant Positive :=
              Positive (Number_Dimensions (Get_Ada_Node (+L_Type)));
            Check : constant W_Pred_Id := New_Length_Equality
              (Left_Arr  => Tmp,
               Right_Arr => Lval,
               Dim       => Dim);

         begin
            T :=
              Sequence
                (New_Located_Assert
                   (Stmt, Check, VC_Length_Check, EW_Assert),
                 +Tmp);
            T := +Binding_For_Temp (Ada_Node => Empty,
                                    Domain   => EW_Prog,
                                    Tmp      => Lval,
                                    Context  => +T);
         end;

      elsif Disc_Check then

         --  Discriminants should be preserved by assignment except if the
         --  object is not constrained.

         declare
            Ty    : constant Entity_Id := Get_Ada_Node (+L_Type);
            Check : W_Expr_Id := +True_Pred;
            Lval  : constant W_Expr_Id :=
              New_Temp_For_Expr
                (Transform_Expr (Lvalue, EW_Pterm, Body_Params), True);
            Discr : Node_Id := (if Count_Discriminants (Ty) > 0
                                then First_Discriminant (Ty)
                                else Empty);
            D_Ty  : constant Entity_Id := Retysp (Ty);
         begin
            while Present (Discr) loop
               declare
                  Input_Discr    : constant W_Expr_Id :=
                    New_Ada_Record_Access
                      (Empty, EW_Term, Tmp, Discr, D_Ty);
                  Expected_Discr : constant W_Expr_Id :=
                    New_Ada_Record_Access
                      (Empty, EW_Term, Lval, Discr, D_Ty);
               begin
                  Check :=
                    New_And_Then_Expr
                      (Domain => EW_Pred,
                       Left   => Check,
                       Right  =>
                         New_Call
                           (Domain => EW_Pred,
                            Name   => Why_Eq,
                            Typ    => EW_Bool_Type,
                            Args   => (+Input_Discr, +Expected_Discr)));
               end;
               Next_Discriminant (Discr);
            end loop;

            if Has_Defaulted_Discriminants (Ty) then
               Check := New_Conditional
                 (Domain      => EW_Pred,
                  Condition   =>
                    New_Constrained_Attribute_Expr (Lvalue, EW_Term),
                  Then_Part   => Check);
            end if;

            T :=
              Sequence
                (New_Located_Assert
                   (Stmt, +Check, VC_Discriminant_Check, EW_Assert),
                 +Tmp);
            T := +Binding_For_Temp (Ada_Node => Empty,
                                    Domain   => EW_Prog,
                                    Tmp      => Lval,
                                    Context  => +T);
         end;
      end if;

      --  If the right hand side is a classwide type, introduce a tag check. Do
      --  not introduce this check for calls with dispatching results as in
      --  this case the tag will depend on the context.

      if Is_Class_Wide_Type (Etype (Lvalue)) and then
        not Is_Tag_Indeterminate (Expression (Stmt))
      then
         declare
            Lval  : constant W_Expr_Id :=
              New_Temp_For_Expr
                (Transform_Expr (Lvalue, EW_Pterm, Body_Params), True);
            Pred : constant W_Pred_Id :=
              New_Call
                (Name => Why_Eq,
                 Typ  => EW_Bool_Type,
                 Args =>
                   (1 =>
                      New_Tag_Access
                        (Name => Lval, Domain => EW_Term,
                         Ty   => Etype (Lvalue)),
                    2 =>
                      New_Tag_Access
                        (Name => Tmp, Domain => EW_Term,
                         Ty   => Get_Ada_Node (+Get_Type (Tmp)))));
         begin
            T :=
              Sequence
                (New_Located_Assert
                   (Stmt, +Pred, VC_Tag_Check, EW_Assert),
                 +Tmp);
            T := +Binding_For_Temp (Ada_Node => Empty,
                                    Domain   => EW_Prog,
                                    Tmp      => Lval,
                                    Context  => +T);
         end;
      end if;

      T := +Binding_For_Temp (Empty, EW_Prog, Tmp, +T);

      --  If a move may be needed, force the use of a temporary to hold
      --  the value of the expression including any moves. This is because
      --  New_Assignment does not expect the rhs expression to modify the
      --  target of the assignment.

      if Is_Deep (Typ)
        and then not Is_Anonymous_Access_Type (Typ)
      then
         declare
            Tmp : W_Expr_Id;
         begin
            Insert_Move_Of_Deep_Parts (Stmt    => Stmt,
                                       Lhs_Typ => Typ,
                                       Expr    => T);
            Tmp := New_Temp_For_Expr (+T);

            --  Check that the assignment does not cause a memory leak. This
            --  is done after moves, so that we properly handle the case where
            --  the target of the assignment is moved by the expression of the
            --  assignment, e.g. an aggregate with the target as element. This
            --  also deals with the special case X:=X so that we avoid issuing
            --  a message here.

            T := +Binding_For_Temp
              (Empty, EW_Prog, Tmp,
               +Sequence
                 (Check_No_Memory_Leaks (Stmt, Lvalue),
                  Gnat2Why.Expr.New_Assignment
                    (Ada_Node => Stmt,
                     Lvalue   => Lvalue,
                     Expr     => +Tmp)));
         end;

      --  Normal assignment that does not involve any move

      else
         T := Gnat2Why.Expr.New_Assignment
           (Ada_Node => Stmt,
            Lvalue   => Lvalue,
            Expr     => T);
      end if;

      --  Update pledge of local borrowers

      if Nkind (Lvalue) in N_Identifier | N_Expanded_Name
        and then Is_Local_Borrower (Entity (Lvalue))
      then
         T := Sequence
           (New_Pledge_Update_From_Assignment
              (Brower  => Entity (Lvalue),
               Path    => Expression (Stmt)),
            T);
      end if;
      return T;
   end Transform_Assignment_Statement;

   -----------------------------
   -- Transform_Attribute_Old --
   -----------------------------

   function Transform_Attribute_Old
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
   begin
      --  Do not generate old when they are not allowed (eg in postconditions
      --  of functions or inside prefixes of 'Old attributes). When the
      --  expression contains no variables, we may still need to generate old
      --  in special cases (pledge functions). In these cases, we will use the
      --  map for old. When we create old why3 nodes, the expression should
      --  contain variable (or Why3 will complain).

      if Params.Old_Policy = Ignore
        or else (Params.Old_Policy = As_Old
                 and then Get_Variables_For_Proof (Expr, Expr).Is_Empty)
      then
         return Transform_Expr (Expr, Domain, Params);
      end if;

      --  Expressions that cannot be translated to predicates directly are
      --  translated to (boolean) terms, and compared to "True".

      if Domain = EW_Pred then
         return
           New_Call
             (Ada_Node => Expr,
              Domain   => EW_Pred,
              Typ      => EW_Bool_Type,
              Name     => Why_Eq,
              Args     =>
                (1 => +Transform_Attribute_Old (Expr, EW_Term, Params),
                 2 => +True_Term));

      --  Use the map for old when references are not allowed

      elsif Params.Old_Policy = Use_Map then
         return +Name_For_Old (Expr);
      else
         return New_Old (Expr   => Transform_Expr (Expr, Domain, Params),
                         Domain => Domain);
      end if;
   end Transform_Attribute_Old;

   --------------------
   -- Transform_Attr --
   --------------------

   function Transform_Attr
     (Expr         : Node_Id;
      Domain       : EW_Domain;
      Params       : Transformation_Params;
      Expected_Typ : W_Type_Id) return W_Expr_Id
   is
      Aname   : constant Name_Id      := Attribute_Name (Expr);
      Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
      Var     : constant Node_Id      := Prefix (Expr);
      T       : W_Expr_Id;

   begin
      --  The attributes supported here must be a subset of those
      --  supported by a language as a whole. This case statement
      --  must therefore maintain that relationship with that in
      --  SPARK_Definition.Mark_Attribute_Reference.
      case Attr_Id is
         when Attribute_Result =>
            if Result_Is_Mutable then
               T :=
                 New_Deref
                   (Ada_Node => Expr,
                    Right    => Result_Name,
                    Typ      => Get_Type (+Result_Name));
            else
               T := +Result_Name;
            end if;

         when Attribute_Old =>
            T := Transform_Attribute_Old (Var, Domain, Params);

         when Attribute_Pred
            | Attribute_Succ
         =>
            --  'Succ and 'Pred on floating-point types are modelled as calls
            --  to logic functions next_representable and prev_representable
            --  for the corresponding type. The value of these functions should
            --  only be specified for values of the argument that do not lead
            --  to an overflow, so that a possible overflow check failure
            --  may be detected when computing Float'Succ(Float'Last) or
            --  Float'Pred(Float'First).

            if Is_Floating_Point_Type (Etype (Var)) then
               declare
                  W_Type : constant W_Type_Id := Base_Why_Type (Etype (Var));
                  Oper : constant W_Identifier_Id :=
                    (if Attr_Id = Attribute_Pred then
                        MF_Floats (W_Type).Prev_Rep
                     else
                        MF_Floats (W_Type).Next_Rep);
                  Arg : constant W_Expr_Id :=
                    Transform_Expr (First (Expressions (Expr)),
                                    W_Type,
                                    Domain,
                                    Params);
               begin
                  T := New_Call (Ada_Node => Expr,
                                 Domain   => Domain,
                                 Name     => Oper,
                                 Args     => (1 => Arg),
                                 Typ      => W_Type);
               end;

            --  For all discrete and fixed-point types, 'Succ is modelled as
            --  adding 1 to the representation value, and 'Pred is modelled
            --  as subtracting 1 to the representation value.

            elsif Is_Modular_Integer_Type (Etype (Var)) then
               declare
                  W_Type : constant W_Type_Id := Base_Why_Type (Etype (Var));
                  Op     : constant N_Op :=
                    (if Attr_Id = Attribute_Succ then
                        N_Op_Add
                     else
                        N_Op_Subtract);
                  Old    : W_Expr_Id;
                  Offset : constant W_Expr_Id :=
                    New_Modular_Constant (Typ => W_Type,
                                          Value => Uint_1);
                  NType : constant Node_Id := Etype (Expr);
               begin
                  Old := Transform_Expr (First (Expressions (Expr)),
                                         W_Type,
                                         Domain,
                                         Params);

                  T := New_Binary_Op_Expr (Op          => Op,
                                           Left        => Old,
                                           Right       => Offset,
                                           Left_Type   => NType,
                                           Right_Type  => NType,
                                           Return_Type => NType,
                                           Domain      => Domain,
                                           Ada_Node    => Expr);
               end;

            else
               declare
                  Op     : constant W_Identifier_Id :=
                    (if Attr_Id = Attribute_Succ then Int_Infix_Add
                     else Int_Infix_Subtr);
                  Old    : W_Expr_Id;
                  Offset : W_Expr_Id;
                  A_Type : constant Entity_Id := Etype (Var);
                  W_Type : W_Type_Id;

               begin
                  if Is_Discrete_Type (A_Type) then
                     W_Type := EW_Int_Type;
                     Offset := New_Integer_Constant (Value => Uint_1);
                  else
                     pragma Assert (Is_Fixed_Point_Type (A_Type));
                     W_Type := Base_Why_Type (A_Type);
                     Offset := New_Fixed_Constant
                       (Value => Uint_1, Typ => W_Type);
                  end if;

                  Old := Transform_Expr (First (Expressions (Expr)),
                                         W_Type,
                                         Domain,
                                         Params);

                  T :=
                    New_Call
                      (Ada_Node => Expr,
                       Domain   => Domain,
                       Name     => Op,
                       Args     => (1 => Old, 2 => Offset),
                       Typ      => W_Type);
               end;
            end if;

         when Attribute_Pos =>
            T := Transform_Expr (First (Expressions (Expr)),
                                 EW_Int_Type,
                                 Domain,
                                 Params);

         when Attribute_Enum_Rep =>
            declare
               Args   : constant List_Id := Expressions (Expr);
               Arg    : constant Node_Id :=
                 (if Is_Non_Empty_List (Args) then First (Args)
                  else Prefix (Expr));
               Arg_Ty : constant Entity_Id := Retysp (Etype (Arg));
            begin
               if Is_Enumeration_Type (Arg_Ty)
                 and then Has_Enumeration_Rep_Clause (Arg_Ty)
               then
                  T := New_Call
                    (Ada_Node => Expr,
                     Domain   => Domain,
                     Name     => E_Symb (Arg_Ty, WNE_Pos_To_Rep),
                     Args     => (1 => Transform_Expr (Arg,
                                  EW_Int_Type,
                                  Domain,
                                  Params)),
                     Typ      => EW_Int_Type);
               else
                  T := Transform_Expr (Arg,
                                       EW_Int_Type,
                                       Domain,
                                       Params);
               end if;
            end;

         when Attribute_Val =>
            declare
               Val_Type : constant W_Type_Id :=
                 Type_Of_Node (Base_Type (Entity (Var)));
            begin
               T := Transform_Expr (First (Expressions (Expr)),
                                    Val_Type,
                                    Domain,
                                    Params);
            end;

         when Attribute_First
            | Attribute_Last
            | Attribute_Length
         =>
            declare
               Ty_Ent : constant Entity_Id :=
                 Retysp (Etype (Var));
            begin

               case Ekind (Ty_Ent) is
                  when Array_Kind =>
                     declare
                        Arr_Ty : constant Entity_Id :=
                          (if Nkind (Var) in N_Identifier | N_Expanded_Name
                           and then Is_Type (Entity (Var))
                           then Entity (Var)
                           else Etype (Var));
                        Dim    : constant Positive :=
                          (if Present (Expressions (Expr)) then
                              Positive
                             (UI_To_Int (Intval (First (Expressions (Expr)))))
                           else 1);
                        B_Exp  : constant W_Type_Id :=
                          Base_Why_Type_No_Bool (Expected_Typ);
                        B_Rng  : constant W_Type_Id :=
                          Base_Why_Type_No_Bool
                            (Nth_Index_Type (Retysp (Arr_Ty), Dim));
                        Typ    : constant W_Type_Id :=
                          (if not Why_Type_Is_BitVector (B_Exp)
                           or else not Why_Type_Is_BitVector (B_Rng)
                           or else (BitVector_Type_Size (B_Rng) = Uint_64
                             and then Domain = EW_Prog)
                           then EW_Int_Type else EW_BitVector_64_Type);
                        --  Typ is only used for the computation of 'Length.
                        --  On 64 bv, in the program domain, use EW_Int_Type so
                        --  that potential range or overflow checks can be
                        --  applied. Do computation on bitvectors only if the
                        --  array ranges over bitvectors as otherwise the
                        --  conversion of 'First and 'Last to Typ may be
                        --  incorrect.

                     begin
                        --  Array_Type'First/Last/Length

                        if Nkind (Var) in N_Identifier | N_Expanded_Name
                          and then Is_Type (Entity (Var))
                        then
                           T := Get_Array_Attr (Domain => Domain,
                                                Ty     => Entity (Var),
                                                Attr   => Attr_Id,
                                                Dim    => Dim,
                                                Typ    => Typ);

                        --  Object'First/Last/Length

                        else
                           declare
                              Why_Expr : constant W_Expr_Id :=
                                Transform_Expr (Var, Domain, Params);
                           begin
                              T := Get_Array_Attr
                                (Domain, Why_Expr, Attr_Id, Dim, Typ => Typ);
                              if Domain = EW_Prog then
                                 T := +Sequence
                                   (New_Ignore (Prog => +Why_Expr), +T);
                              end if;
                           end;
                        end if;
                     end;

                  when Discrete_Kind | Real_Kind =>
                     T := New_Attribute_Expr
                       (Etype (Var), Domain, Attr_Id, Params);

                  when others =>

                     --  All possible cases should have been handled before
                     --  this point.

                     raise Program_Error;
               end case;
            end;

         when Attribute_Loop_Entry =>
            Loop_Entry : declare

               function Is_Loop_Stmt (N : Node_Id) return Boolean is
                 (Nkind (N) = N_Loop_Statement);

               function Enclosing_Loop_Stmt is new
                 First_Parent_With_Property (Is_Loop_Stmt);

               Arg       : constant Node_Id := First (Expressions (Expr));
               Loop_Id   : Entity_Id;
               Loop_Stmt : Node_Id;

            begin
               --  The loop to which attribute Loop_Entry applies is either
               --  identified explicitly in argument, or, if Loop_Entry takes
               --  no arguments, it is the innermost enclosing loop.

               if Present (Arg) then
                  Loop_Id := Entity (Arg);

               --  Climb the parent chain to find the nearest enclosing loop

               else
                  Loop_Stmt := Enclosing_Loop_Stmt (Expr);
                  Loop_Id := Entity (Identifier (Loop_Stmt));
               end if;

               pragma Assert (Domain /= EW_Pred
                               and then Params.Phase in Generate_VCs);

               T := +Name_For_Loop_Entry (Var, Loop_Id);
            end Loop_Entry;

         when Attribute_Modulus =>
            T := New_Attribute_Expr (Etype (Var), Domain, Attr_Id);

         when Attribute_Mod =>
            declare
               Arg         : constant Node_Id := First (Expressions (Expr));
               Arg_BTyp    : constant W_Type_Id := Base_Why_Type (Arg);

               --  S'Mod for subtype S returns a value of type S'Base
               Target_Type : constant W_Type_Id :=
                 Base_Why_Type (Base_Type (Etype (Var)));

            begin
               --  If the argument is a bitvector we do the modulo on
               --  bitvectors.

               if Why_Type_Is_BitVector (Arg_BTyp) then
                  declare
                     Arg_Modulus : constant Uint := Modulus (Etype (Arg));
                     Var_Modulus : constant Uint := Modulus (Etype (Var));
                     Arg_Expr    : W_Expr_Id;
                     Mod_Expr    : W_Expr_Id;

                  begin
                     --  If the modulus of the argument is greater than the
                     --  value of the modulo operation, then apply the modulo.

                     if Arg_Modulus > Var_Modulus then
                        Arg_Expr :=
                          Transform_Expr (Arg, Arg_BTyp, Domain, Params);

                        --  If the modulo comes from a builtin type, we use the
                        --  modulus valus from Why3 theory.

                        if Get_EW_Type (Var) = EW_Builtin then
                           Mod_Expr :=
                             Insert_Simple_Conversion
                               (Domain => EW_Term,
                                Expr   =>
                                  +MF_BVs (Base_Why_Type (Var)).Two_Power_Size,
                                To     => Arg_BTyp);

                        --  Otherwise, we retrieve the value of the Modulus
                        --  attribute.

                        else
                           Mod_Expr :=
                             New_Attribute_Expr
                               (Etype (Var), Domain, Attribute_Modulus);
                        end if;

                        T := Insert_Simple_Conversion
                               (Domain => EW_Term,
                                Expr   =>
                                  New_Call (Ada_Node => Expr,
                                            Domain   => Domain,
                                            Name     => MF_BVs (Arg_BTyp).Urem,
                                            Args     =>
                                              (1 => Arg_Expr,
                                               2 => Mod_Expr),
                                            Typ      => Arg_BTyp),
                                To => Target_Type);

                     --  If the modulus of the argument is no greater than the
                     --  value of the modulo operation, then simply convert the
                     --  value to the new type.

                     else
                        T := Insert_Simple_Conversion
                               (Domain => EW_Term,
                                Expr   =>
                                  Transform_Expr (Arg, Domain, Params),
                                To     => Target_Type);
                     end if;
                  end;

               --  If not, we do the modulo on integer and convert back

               else
                  T := Insert_Simple_Conversion
                    (Domain => EW_Term,
                     Expr   =>
                       New_Call (Ada_Node => Expr,
                           Domain => Domain,
                           Name   => M_Int_Div.Mod_Id,
                           Args   =>
                             (1 => Transform_Expr (Arg,
                                                   EW_Int_Type,
                                                   Domain,
                                                   Params),
                              2 =>
                                (if Get_EW_Type (Var) = EW_Builtin then
                                 --  if we're builtin, i.e., not abstract,
                                 --  we use standard modulus from why theory
                                   +MF_BVs (Base_Why_Type (Var)).Two_Power_Size

                                 else
                                 --  else we refer to the attribute modulus
                                   Insert_Simple_Conversion
                                     (Domain => EW_Term,
                                      Expr   =>
                                        New_Attribute_Expr
                                          (Etype (Var),
                                           Domain,
                                           Attribute_Modulus),
                                       To     => EW_Int_Type))),
                                 Typ   => EW_Int_Type),
                     To     => Target_Type);
               end if;
            end;

         --  We generate the expression String.to_string (image_func (arg)),
         --  where arg may be either the prefix in the notation X'Image, or
         --  the argument in notation S'Image(X).

         when Attribute_Image
            | Attribute_Img
         =>
            declare
               Arg : constant Node_Id :=
                 (if Present (Expressions (Expr)) then
                    First (Expressions (Expr))
                  else
                    Var);
            begin
               T := New_Call (Ada_Node => Expr,
                              Domain   => Domain,
                              Name     => +New_Attribute_Expr
                                (Etype (Var), Domain, Attribute_Image),
                              Args     =>
                                (1 => Transform_Expr (Arg,
                                                      Base_Why_Type (Var),
                                                      Domain,
                                                      Params)));

               --  To_string takes as a second argument the maximum size of the
               --  image of the corresponding type.

               T := New_Call (Ada_Node => Expr,
                              Domain   => Domain,
                              Name     => To_String_Id,
                              Args     =>
                                (1 => T,
                                 2 => New_Integer_Constant
                                   (Value => Max_Size_Of_Img_Attr
                                        (Retysp (Etype (Var))))),
                              Typ      => EW_Abstract (Standard_String));
            end;

         when Attribute_Size
            | Attribute_Value_Size
            | Attribute_Object_Size
         =>
            --  For arrays and records we do not know the exact value of
            --  attribute size, which is decided by the back-end when
            --  generating executable code. Instead, we generate call to an
            --  uninterpreted function, either:
            --
            --  * "value__size", which corresponds to
            --  ** Type'Size in Ada
            --  ** Type'Value_Size in GNAT
            --  ** RM_Size field in GNAT AST
            --
            --  or
            --
            --  * "object__size", which corresponds to
            --  ** Object'Size in Ada
            --  ** Type'Object_Size in GNAT
            --  ** Esize field in GNAT AST

            Size_Attributes : declare
               subtype Size_Attributes is Attribute_Id with
                 Static_Predicate => Size_Attributes in Attribute_Size
                                                      | Attribute_Value_Size
                                                      | Attribute_Object_Size;

               function Object_Size (Typ : Entity_Id) return W_Expr_Id is
                 (New_Call (Ada_Node => Expr,
                            Domain   => Domain,
                            Name     => E_Symb (Typ, WNE_Attr_Object_Size),
                            Typ      => EW_Int_Type))
               with Pre => Is_Type (Typ);
               --  Return the expression corresponding to attribute Object_Size
               --  applied to type [Typ]. [Type_Prefix] is True for a type
               --  prefix and False for an object prefix. In the program
               --  domain, generate checks for an object prefix with
               --  attribute Size.

               Has_Type_Prefix : constant Boolean :=
                 Nkind (Var) in N_Identifier | N_Expanded_Name
                   and then Is_Type (Entity (Var));

            --  Start of processing for Size_Attributes

            begin
               if Has_Type_Prefix then
                  case Size_Attributes'(Attr_Id) is
                     when Attribute_Size
                        | Attribute_Value_Size
                     =>
                        T :=
                          New_Attribute_Expr (Entity (Var), Domain, Attr_Id);

                     when Attribute_Object_Size =>
                        T := Object_Size (Entity (Var));
                  end case;

               --  Only attribute Size applies to an object. It is either
               --  the specified value of Size for the object, or the same
               --  as Typ'Object_Size for the type of the object.

               else
                  pragma Assert (Attr_Id = Attribute_Size);

                  if Known_Object_Size (Etype (Var)) then
                     T := New_Integer_Constant (Expr,
                                                Object_Size (Etype (Var)));
                  else
                     T := Object_Size (Etype (Var));
                  end if;

                  --  In the program domain, translate the object itself to
                  --  generate any necessary checks.

                  if Domain = EW_Prog then
                     T := New_Binding
                            (Name    =>
                               New_Temp_Identifier (Typ => Get_Type (+T)),
                             Domain  => Domain,
                             Def     =>
                               +Transform_Expr (Var, Domain, Params),
                             Context => +T,
                             Typ     => Get_Type (+T));
                  end if;
               end if;
            end Size_Attributes;

         when Attribute_Value =>
            declare
               Why_Str : constant W_Type_Id :=
                           EW_Abstract (Standard_String);
               Arg     : constant W_Expr_Id :=
                           Transform_Expr (First (Expressions (Expr)),
                                           Why_Str,
                                           Domain,
                                           Params);
               Func    : constant W_Identifier_Id :=
                           +New_Attribute_Expr (Etype (Var), Domain, Attr_Id);
            begin
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => Of_String_Id,
                    Args     => (1 => Arg));
               if Domain = EW_Prog then
                  T := New_VC_Call
                    (Ada_Node => Expr,
                     Domain   => Domain,
                     Name     => To_Program_Space (Func),
                     Progs    => (1 => T),
                     Reason   => VC_Precondition,
                     Typ      => Base_Why_Type (Var));
               else
                  T := New_Call
                    (Ada_Node => Expr,
                     Domain   => Domain,
                     Name     => Func,
                     Args     => (1 => T),
                     Typ      => Base_Why_Type (Var));
               end if;
            end;

         when Attribute_Update =>
            T := Transform_Delta_Aggregate
              (Ada_Node => Expr,
               Pref     => Prefix (Expr),
               Aggr     => First (Expressions (Expr)),
               Domain   => Domain,
               Params   => Params);

         when Attribute_Ceiling
            | Attribute_Floor
            | Attribute_Rounding
            | Attribute_Truncation
         =>
            declare
               Typ : constant W_Type_Id := Base_Why_Type (Etype (Var));
               Arg  : constant W_Expr_Id :=
                        Transform_Expr (First (Expressions (Expr)),
                                        Typ,
                                        Domain,
                                        Params);
               Func : constant W_Identifier_Id :=
                             (if Attr_Id = Attribute_Ceiling then
                                 MF_Floats (Typ).Ceil
                              elsif Attr_Id = Attribute_Floor then
                                 MF_Floats (Typ).Floor
                              elsif Attr_Id = Attribute_Rounding then
                                 MF_Floats (Typ).Rounding
                              else MF_Floats (Typ).Truncate);
            begin
               T := New_Call (Ada_Node => Expr,
                              Domain   => Domain,
                              Name     => Func,
                              Args     => (1 => Arg),
                              Typ      => Typ);
            end;

         when Attribute_Remainder =>
            declare
               Ada_Ty : constant Entity_Id := Etype (Expr);
               Base   : constant W_Type_Id := Base_Why_Type (Ada_Ty);
               Arg_1  : constant W_Expr_Id :=
                 Transform_Expr (First (Expressions (Expr)),
                                 Base,
                                 Domain,
                                 Params);
               Arg_2  : constant W_Expr_Id :=
                 Transform_Expr (Next (First (Expressions (Expr))),
                                 Base,
                                 Domain,
                                 Params);
            begin
               if Domain = EW_Prog
               then
                  --  The front end does not insert a Do_Division_Check flag on
                  --  remainder attribute so we systematically do the check.
                  T := New_VC_Call
                    (Ada_Node => Expr,
                     Name     => To_Program_Space (MF_Floats (Base).Remainder),
                     Progs    => (1 => Arg_1,
                                  2 => Arg_2),
                     Reason   => VC_Division_Check,
                     Domain   => Domain,
                     Typ      => Base);
               else
                  T := New_Call
                    (Ada_Node => Expr,
                     Name     => MF_Floats (Base).Remainder,
                     Args     => (1 => Arg_1,
                                  2 => Arg_2),
                     Domain   => Domain,
                     Typ      => Base);
               end if;
            end;

         when Attribute_Min
            | Attribute_Max
         =>
            declare
               Ada_Ty : constant Entity_Id := Retysp (Etype (Expr));
               Base   : constant W_Type_Id := Base_Why_Type_No_Bool (Ada_Ty);
               Arg1   : constant W_Expr_Id :=
                 Transform_Expr (First (Expressions (Expr)),
                                 Base,
                                 Domain,
                                 Params);
               Arg2   : constant W_Expr_Id :=
                 Transform_Expr (Next (First (Expressions (Expr))),
                                 Base,
                                 Domain,
                                 Params);
               Func   : constant W_Identifier_Id :=
                 (if Is_Discrete_Type (Ada_Ty)
                    or else Is_Fixed_Point_Type (Ada_Ty)
                  then
                      (if Is_Modular_Integer_Type (Ada_Ty) then
                         (if Attr_Id = Attribute_Min
                          then MF_BVs (Base).BV_Min
                          else MF_BVs (Base).BV_Max)
                       else
                         (if Attr_Id = Attribute_Min
                          then M_Int_Minmax.Min
                          else M_Int_Minmax.Max))
                  else (if Attr_Id = Attribute_Min
                        then MF_Floats (Base).Min
                        else MF_Floats (Base).Max));
            begin
               T := New_Call (Ada_Node => Expr,
                              Domain   => Domain,
                              Name     => Func,
                              Args     => (1 => Arg1, 2 => Arg2),
                              Typ      => Base);
            end;

         --  Currently support attribute Valid by assuming it always evaluates
         --  to True.

         when Attribute_Valid =>
            if Domain = EW_Prog then
               declare
                  Why_Expr : constant W_Expr_Id :=
                    Transform_Expr (Var, Domain, Params);
               begin
                  T := +Sequence (New_Ignore (Prog => +Why_Expr), +True_Term);
               end;
            else
               T := +True_Term;
            end if;

         when Attribute_Constrained =>
            T := New_Constrained_Attribute_Expr (Domain => Domain,
                                                 Prefix => Var);
            if Domain = EW_Prog then
               T := +Sequence
                 (New_Ignore
                    (Prog => +Transform_Expr (Var, Domain, Params)), +T);
            end if;

         when Attribute_Address =>
            T := +E_Symb (Entity (Var), WNE_Attr_Address);

         when Attribute_Callable =>
            T := +True_Term;

         when Attribute_Terminated =>
            T := +False_Term;

         when Attribute_Component_Size =>
            declare
               Has_Type_Prefix : constant Boolean :=
                 Nkind (Var) in N_Identifier | N_Expanded_Name
                   and then Is_Type (Entity (Var));
               Typ : constant Entity_Id :=
                 (if Has_Type_Prefix then Entity (Var) else Etype (Var));
            begin
               T := New_Attribute_Expr (Typ, Domain, Attr_Id);

               --  In the program domain, translate the object itself to
               --  generate any necessary checks. Note that Component_Size may
               --  only be specified explicitly for a type, not for an object,
               --  so there is no reason here to call Known_Component_Size for
               --  more precise handling of the value of the attribute.

               if not Has_Type_Prefix
                 and then Domain = EW_Prog
               then
                  T := New_Binding
                         (Name    =>
                            New_Temp_Identifier (Typ => Get_Type (+T)),
                          Domain  => Domain,
                          Def     =>
                            +Transform_Expr (Var, Domain, Params),
                          Context => +T,
                          Typ     => Get_Type (+T));
               end if;
            end;

         when Attribute_Alignment =>
            declare
               Has_Type_Prefix : constant Boolean :=
                 Nkind (Var) in N_Has_Entity
                   and then Present (Entity (Var))
                   and then Is_Type (Entity (Var));
            begin
               --  Alignment may be specified explicitly on the type or
               --  object. When specified on the type, the frontend replaces
               --  T'Alignment by its value. When specified on the object,
               --  we only support cases where the alignment is known.

               if Has_Type_Prefix then
                  declare
                     Typ : constant Entity_Id := Entity (Var);
                  begin
                     if Known_Alignment (Typ) then
                        T := New_Integer_Constant (Expr, Alignment (Typ));
                     else
                        T := New_Attribute_Expr (Typ, Domain, Attr_Id);
                     end if;
                  end;
               else
                  pragma Assert (Present (Entity (Var))
                                   and then Known_Alignment (Entity (Var)));
                  T := New_Integer_Constant (Expr, Alignment (Entity (Var)));
               end if;

               --  In the program domain, translate the object itself to
               --  generate any necessary checks.

               if not Has_Type_Prefix
                 and then Domain = EW_Prog
               then
                  T := New_Binding
                         (Name    =>
                            New_Temp_Identifier (Typ => Get_Type (+T)),
                          Domain  => Domain,
                          Def     =>
                            +Transform_Expr (Var, Domain, Params),
                          Context => +T,
                          Typ     => Get_Type (+T));
               end if;
            end;

         when Attribute_First_Bit =>
            declare
               Component : constant Entity_Id := Entity (Selector_Name (Var));

            begin
               if Known_Component_First_Bit (Component) then
                  return New_Integer_Constant
                    (Expr, Component_First_Bit (Component));
               else
                  declare
                     Name : constant W_Identifier_Id :=
                       E_Symb (Component, WNE_Attr_First_Bit);

                  begin
                     return New_Call (Ada_Node => Expr,
                                      Domain   => Domain,
                                      Name     => Name,
                                      Typ      => EW_Int_Type);
                  end;
               end if;
            end;

         when Attribute_Last_Bit =>
            declare
               Component : constant Entity_Id := Entity (Selector_Name (Var));

            begin
               if Known_Component_Last_Bit (Component) then
                  return New_Integer_Constant
                    (Expr, Component_Last_Bit (Component));

               else
                  declare
                     Name : constant W_Identifier_Id :=
                       E_Symb (Component, WNE_Attr_Last_Bit);

                  begin
                     return New_Call (Ada_Node => Expr,
                                      Domain   => Domain,
                                      Name     => Name,
                                      Typ      => EW_Int_Type);
                  end;
               end if;
            end;

         when Attribute_Position =>
            declare
               Component : constant Entity_Id := Entity (Selector_Name (Var));

            begin
               if Present (Component_Clause (Component)) then
                  return New_Integer_Constant
                    (Expr, Component_Position (Component));
               else
                  declare
                     Name : constant W_Identifier_Id :=
                       E_Symb (Component, WNE_Attr_Position);

                  begin
                     return New_Call (Ada_Node => Expr,
                                      Domain   => Domain,
                                      Name     => Name,
                                      Typ      => EW_Int_Type);
                  end;
               end if;
            end;

         --  The Initialized attribute is used to express that a value has been
         --  initialized. To remain as close as possible to the executable
         --  semantics of the attribute, proof does not assume that
         --  'Initialized necessarily returns False on uninitialized data.

         when Attribute_Initialized =>
            declare
               Expr : constant W_Expr_Id :=
                 Transform_Expr
                   (Expr    => Var,
                    Domain  => Domain,
                    Params  => Params);
            begin
               return Compute_Is_Initialized
                 (Etype (Var), Expr, Params.Ref_Allowed, Domain);
            end;

         when others =>
            Ada.Text_IO.Put_Line ("[Transform_Attr] not implemented: "
                                  & Attribute_Id'Image (Attr_Id));
            raise Not_Implemented;
      end case;

      return T;
   end Transform_Attr;

   -------------------------------
   -- Transform_Block_Statement --
   -------------------------------

   function Transform_Block_Statement (N : Node_Id) return W_Prog_Id is
      Core : W_Prog_Id :=
        Transform_Statements_And_Declarations
          (Statements (Handled_Statement_Sequence (N)));
   begin
      if Present (Declarations (N)) then

         --  Havoc all entities borrowed in the block

         Core := Sequence
           ((1 => Core,
             2 => +Havoc_Borrowed_From_Block (N),
             3 => Check_No_Memory_Leaks_At_End_Of_Scope (Declarations (N))));

         return Transform_Declarations_Block (Declarations (N), Core);
      else
         return Core;
      end if;
   end Transform_Block_Statement;

   --------------------------
   -- Transform_Compare_Op --
   --------------------------

   function Transform_Compare_Op
     (Op     : N_Op_Compare;
      Ty     : W_Type_Id;
      Domain : EW_Domain)
      return W_Identifier_Id is
   begin
      if Domain = EW_Term then
         if Ty in EW_Int_Type | EW_Bool_Type
           or else Why_Type_Is_Fixed (Ty)
         then
            case Op is
               when N_Op_Gt => return M_Integer.Bool_Gt;
               when N_Op_Lt => return M_Integer.Bool_Lt;
               when N_Op_Eq => return M_Integer.Bool_Eq;
               when N_Op_Ne => return M_Integer.Bool_Ne;
               when N_Op_Ge => return M_Integer.Bool_Ge;
               when N_Op_Le => return M_Integer.Bool_Le;
            end case;
         elsif Why_Type_Is_Float (Ty) then
            case Op is
               when N_Op_Gt => return MF_Floats (Ty).Bool_Gt;
               when N_Op_Lt => return MF_Floats (Ty).Bool_Lt;
               when N_Op_Eq => return MF_Floats (Ty).Bool_Eq;
               when N_Op_Ne => return MF_Floats (Ty).Bool_Ne;
               when N_Op_Ge => return MF_Floats (Ty).Bool_Ge;
               when N_Op_Le => return MF_Floats (Ty).Bool_Le;
            end case;
         elsif Ty = EW_Bool_Type then
            case Op is
               when N_Op_Gt => return M_Boolean.Bool_Gt;
               when N_Op_Lt => return M_Boolean.Bool_Lt;
               when N_Op_Eq => return M_Boolean.Bool_Eq;
               when N_Op_Ne => return M_Boolean.Bool_Ne;
               when N_Op_Ge => return M_Boolean.Bool_Ge;
               when N_Op_Le => return M_Boolean.Bool_Le;
            end case;
         elsif Why_Type_Is_BitVector (Ty) then
            case Op is
               when N_Op_Gt => return MF_BVs (Ty).Bool_Gt;
               when N_Op_Lt => return MF_BVs (Ty).Bool_Lt;
               when N_Op_Eq => return MF_BVs (Ty).Bool_Eq;
               when N_Op_Ne => return MF_BVs (Ty).Bool_Ne;
               when N_Op_Ge => return MF_BVs (Ty).Bool_Ge;
               when N_Op_Le => return MF_BVs (Ty).Bool_Le;
            end case;
         else
            raise Program_Error;
         end if;
      elsif Ty in EW_Int_Type | EW_Bool_Type
           or else Why_Type_Is_Fixed (Ty)
      then
         case Op is
            when N_Op_Gt => return Int_Infix_Gt;
            when N_Op_Lt => return Int_Infix_Lt;
            when N_Op_Eq => return Why_Eq;
            when N_Op_Ne => return Why_Neq;
            when N_Op_Ge => return Int_Infix_Ge;
            when N_Op_Le => return Int_Infix_Le;
         end case;
      elsif Why_Type_Is_Float (Ty) then
         case Op is
            when N_Op_Gt => return MF_Floats (Ty).Gt;
            when N_Op_Lt => return MF_Floats (Ty).Lt;
            when N_Op_Eq => return MF_Floats (Ty).Eq;
            when N_Op_Ne => return MF_Floats (Ty).Neq;
            when N_Op_Ge => return MF_Floats (Ty).Ge;
            when N_Op_Le => return MF_Floats (Ty).Le;
         end case;
      elsif Why_Type_Is_BitVector (Ty) then
         case Op is
            when N_Op_Gt => return MF_BVs (Ty).Ugt;
            when N_Op_Lt => return MF_BVs (Ty).Ult;
            when N_Op_Eq =>
               if Domain = EW_Pred then
                  return Why_Eq;
               else
                  return MF_BVs (Ty).Prog_Eq;
               end if;
            when N_Op_Ne =>
               if Domain = EW_Pred then
                  return Why_Neq;
               else
                  return MF_BVs (Ty).Prog_Neq;
               end if;
            when N_Op_Ge => return MF_BVs (Ty).Uge;
            when N_Op_Le => return MF_BVs (Ty).Ule;
         end case;
      else
         raise Program_Error;
      end if;
   end Transform_Compare_Op;

   --------------------------
   -- Transform_Comparison --
   --------------------------

   function Transform_Comparison
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
      function Is_Equal_Of_Update (Expr : Node_Id) return Boolean with
        Pre => Has_Array_Type (Etype (Left_Opnd (Expr)));
      --  Return True if Expr is of the form X op E'Update (I => V) where
      --  E is either X'Old or X'Loop_Entry and op is either = or /=.

      function Transform_Equal_Of_Update
        (Expr   : Node_Id;
         Domain : EW_Domain;
         Params : Transformation_Params) return W_Expr_Id
      with Pre => Has_Array_Type (Etype (Left_Opnd (Expr)))
        and then Is_Equal_Of_Update (Expr);
      --  From: X = E'Update (I => V)
      --  construct:
      --    (for all K in X'Range => X (K) = (if K = I then V else E (K)))

      ------------------------
      -- Is_Equal_Of_Update --
      ------------------------

      function Is_Equal_Of_Update (Expr : Node_Id) return Boolean is
         Var  : constant Node_Id :=
           (if Nkind (Left_Opnd (Expr)) = N_Identifier
            then Left_Opnd (Expr) else Right_Opnd (Expr));
         Upd  : constant Node_Id :=
           (if Nkind (Left_Opnd (Expr)) = N_Identifier
            then Right_Opnd (Expr) else Left_Opnd (Expr));
         Pref : constant Node_Id :=
           (if Nkind (Upd) = N_Attribute_Reference
              and then
                Get_Attribute_Id (Attribute_Name (Upd)) = Attribute_Update
            then Prefix (Upd)
            elsif Nkind (Upd) = N_Delta_Aggregate
            then Expression (Upd)
            else Empty);
         --  If Upd is a 'Update attribute or a delta aggregate, Pref is the
         --  node of the updated expression, otherwise it is empty.

      begin
         return Nkind (Expr) in N_Op_Eq | N_Op_Ne

           --  Var must be a variable

           and then Nkind (Var) = N_Identifier

           --  Equality should not have been redefined for Var

           and then
             (not Is_Record_Type (Unchecked_Full_Type (Etype (Var)))
              or else Is_Limited_View (Etype (Var))
              or else No
                (Get_User_Defined_Eq (Base_Type (Etype (Var)))))

           --  Upd should be a 'Update attribute or a delta aggregate

           and then Present (Pref)

           --  whose prefix is a 'Old or 'Loop_Entry attribute

           and then Nkind (Pref) = N_Attribute_Reference
           and then Get_Attribute_Id (Attribute_Name (Pref)) in
                 Attribute_Old | Attribute_Loop_Entry

           --  whose prefix is Var.

           and then Nkind (Prefix (Pref)) = N_Identifier
           and then Entity (Var) = Entity (Prefix (Pref));
      end Is_Equal_Of_Update;

      -------------------------------
      -- Transform_Equal_Of_Update --
      -------------------------------

      function Transform_Equal_Of_Update
        (Expr   : Node_Id;
         Domain : EW_Domain;
         Params : Transformation_Params) return W_Expr_Id is
      begin
         --  This translation is done in the predicate domain to be able to
         --  use quantification. In the Prog domain, we still need some kind
         --  of translation to generate checks.

         if Domain in EW_Terms then
            declare
               Pred : constant W_Expr_Id :=
                 Transform_Equal_Of_Update (Expr, EW_Pred, Params);
            begin
               return Boolean_Expr_Of_Pred (+Pred, Domain);
            end;
         end if;

         declare
            Var           : constant Node_Id :=
              (if Nkind (Left_Opnd (Expr)) = N_Identifier
               then Left_Opnd (Expr) else Right_Opnd (Expr));
            pragma Assert (Nkind (Var) = N_Identifier);
            Upd           : constant Node_Id :=
              (if Nkind (Left_Opnd (Expr)) = N_Identifier
               then Right_Opnd (Expr) else Left_Opnd (Expr));
            pragma Assert
              (Nkind (Upd) in N_Attribute_Reference | N_Delta_Aggregate);
            Arr_Ty        : constant Entity_Id := Etype (Var);

            T             : W_Expr_Id;
            Subdomain     : constant EW_Domain :=
              (if Domain = EW_Pred then EW_Term else Domain);
            Subd_No_Check : constant EW_Domain :=
              (if Domain = EW_Prog then EW_Pterm else Subdomain);
            Assocs        : constant List_Id :=
              (if Nkind (Upd) = N_Delta_Aggregate
               then Component_Associations (Upd)
               else Component_Associations (First (Expressions (Upd))));
            Prefix_N      : constant Node_Id :=
              (if Nkind (Upd) = N_Delta_Aggregate then Expression (Upd)
               else Prefix (Upd));
            Association   : Node_Id := Nlists.First (Assocs);
            Dim           : constant Positive :=
              Positive (Number_Dimensions (Etype (Var)));
            Indexes       : W_Identifier_Array (1 .. Dim);
            --  Indexes inside the array

            Vars          : W_Expr_Array (1 .. Dim);
            --  Expressions used to index arrays at index Indexes

            Guards        : W_Expr_Array
              (1 .. Natural (List_Length (Assocs))) :=
              (others => New_Literal
                 (Domain => Domain,
                  Value  => EW_False,
                  Typ    => EW_Bool_Type));
            --  Expressions for the evaluation of the choices

            Exprs         : W_Expr_Array
              (1 .. Natural (List_Length (Assocs)));
            --  Expressions associated to the choices

            Index         : Node_Id := First_Index (Arr_Ty);
            Num_Assoc     : Positive := 1;

         begin
            --  Store indexes inside Indexes and Vars

            for I in Indexes'Range loop
               Indexes (I) := New_Temp_Identifier
                 (Typ       => Type_Of_Node (Etype (Index)),
                  Base_Name => "index");
               Vars (I) := Insert_Simple_Conversion
                 (Domain => Subd_No_Check,
                  Expr   => +Indexes (I),
                  To     => Base_Why_Type_No_Bool
                    (Get_Typ (Indexes (I))));
               Next_Index (Index);
            end loop;

            --  Compute choices and expressions

            while Present (Association) loop
               declare
                  Choice : Node_Id := First (Choices (Association));
                  Rng    : Node_Id;
                  Guard  : W_Expr_Id;
               begin
                  while Present (Choice) loop

                     --  Transform the choice into a guard

                     case Nkind (Choice) is
                        when N_Range =>
                           pragma Assert (Dim = 1);
                           Rng := Get_Range (Choice);
                           Guard := New_Range_Expr
                             (Domain => Domain,
                              Low    => Transform_Expr
                                (Expr          => Low_Bound (Rng),
                                 Domain        => Subdomain,
                                 Params        => Params,
                                 Expected_Type => Get_Typ
                                   (W_Identifier_Id'(+Vars (1)))),
                              High   => Transform_Expr
                                (Expr          => High_Bound (Rng),
                                 Domain        => Subdomain,
                                 Params        => Params,
                                 Expected_Type => Get_Typ
                                   (W_Identifier_Id'(+Vars (1)))),
                              Expr   => Vars (1));
                        when N_Aggregate =>
                           declare
                              Expr : Node_Id :=
                                Nlists.First (Expressions (Choice));

                           begin
                              pragma Assert
                                (List_Length (Expressions (Choice)) =
                                   Nat (Dim));

                              Guard := New_Literal
                                (Domain => Domain,
                                 Value  => EW_True,
                                 Typ    => EW_Bool_Type);

                              for Tmp_Index of Indexes loop
                                 pragma Assert (Present (Expr));
                                 Guard := New_And_Expr
                                   (Left   => Guard,
                                    Right  => New_Ada_Equality
                                      (Typ    => Get_Ada_Node
                                           (+Get_Typ (Tmp_Index)),
                                       Left   => +Tmp_Index,
                                       Right  => Transform_Expr
                                         (Expr          => Expr,
                                          Domain        => Subdomain,
                                          Params        => Params,
                                          Expected_Type => Get_Typ
                                            (Tmp_Index)),
                                       Domain => Domain),
                                    Domain => Domain);
                                 Next (Expr);
                              end loop;
                           end;
                        when others =>
                           pragma Assert (Dim = 1);
                           Guard := New_Ada_Equality
                             (Typ    => Get_Ada_Node
                                (+Get_Typ (Indexes (1))),
                              Left   => +Indexes (1),
                              Right  => Transform_Expr
                                (Expr          => Choice,
                                 Domain        => Subdomain,
                                 Params        => Params,
                                 Expected_Type => Get_Typ
                                   (W_Identifier_Id'(+Indexes (1)))),
                              Domain => Domain);
                     end case;

                     --  Add the choice to Guards

                     Guards (Num_Assoc) := New_Or_Expr
                       (Left   => Guards (Num_Assoc),
                        Right  => Guard,
                        Domain => Domain);
                     Next (Choice);
                  end loop;

               end;
               Exprs (Num_Assoc) := Transform_Expr
                 (Expr          => Expression (Association),
                  Domain        => Subdomain,
                  Params        => Params,
                  Expected_Type => Type_Of_Node
                    (Component_Type (Arr_Ty)));
               Num_Assoc := Num_Assoc + 1;
               Next (Association);
            end loop;

            --  In the predicate domain, we generate a universally quantified
            --  formula comparing the elements of the array one by one.

            if Domain = EW_Pred then

               T := Insert_Simple_Conversion
                 (Domain => Subdomain,
                  Expr   => New_Array_Access
                    (Ada_Node => Empty,
                     Ar       => Transform_Expr
                       (Expr          => Prefix_N,
                        Domain        => Subdomain,
                        Params        => Params,
                        Expected_Type => Type_Of_Node (Arr_Ty)),
                     Index    => Vars,
                     Domain   => Subd_No_Check),
                  To     => Type_Of_Node (Component_Type (Arr_Ty)));

               --  Construct the conditional by starting from the expression
               --  Upd (I) and add conditions in the reverse order.

               for J in Exprs'Range loop
                  T := New_Conditional
                    (Ada_Node    => Expr,
                     Domain      => Subdomain,
                     Condition   => Guards (J),
                     Then_Part   => Exprs (J),
                     Else_Part   => T,
                     Typ         => Type_Of_Node (Component_Type (Arr_Ty)));
               end loop;

               --  Var (I) is equal to the conditional

               T := New_Ada_Equality
                 (Typ    => Component_Type (Arr_Ty),
                  Domain => Domain,
                  Left   => Insert_Simple_Conversion
                    (Domain => Subdomain,
                     Expr   => New_Array_Access
                       (Ada_Node => Empty,
                        Ar       => Transform_Expr
                          (Expr          => Var,
                           Domain        => Subdomain,
                           Params        => Params,
                           Expected_Type => Type_Of_Node (Arr_Ty)),
                        Index    => Vars,
                        Domain   => Subd_No_Check),
                     To     => Type_Of_Node
                       (Component_Type (Arr_Ty))),
                  Right  => T);

               --  Universally quantify the formula

               for J in Indexes'Range loop
                  T := New_Universal_Quantif
                    (Variables => (1 => Indexes (J)),
                     Labels    => Symbol_Sets.Empty_Set,
                     Var_Type  => Get_Typ (Indexes (J)),
                     Pred      => New_Conditional
                       (Condition => New_Array_Range_Expr
                            (Index_Expr => +Indexes (J),
                             Array_Expr => Transform_Expr
                               (Expr          => Var,
                                Domain        => Subdomain,
                                Params        => Params,
                                Expected_Type => Type_Of_Node (Arr_Ty)),
                             Domain     => EW_Pred,
                             Dim        => J),
                        Then_Part => +T,
                        Typ       => EW_Bool_Type));
               end loop;

               if Nkind (Expr) = N_Op_Ne then
                  T := New_Not (Domain => EW_Pred, Right => T);
               end if;

            --  In the EW_Prog domain, we concentrate on generating the checks.
            --  The expression will be created by lifting the translation in
            --  the predicate domain.

            else
               pragma Assert (Domain = EW_Prog);
               T := +Void;

               --  Instead of a conditional, we generate a sequence to avoid
               --  shadowing checks coming from the first occurrence of
               --  duplicated choices.

               for J in Exprs'Range loop
                  T := +Sequence
                    ((1 => +T,
                      2 => New_Ignore (Prog => +Guards (J)),
                      3 => New_Ignore (Prog => +Exprs (J))));
               end loop;

               --  Link indexes to any expressions using
               --  let bindings and hide the expression inside an ignore block.
               --  Afterward, assume the formula using the translation in the
               --  EW_Pred domain.
               --  ignore { let i = any in ... };
               --  any boolean { forall i. ... }

               for Tmp_Index of Indexes loop
                  T := New_Typed_Binding
                    (Name    => Tmp_Index,
                     Domain  => EW_Prog,
                     Def     => +New_Simpl_Any_Prog
                       (Get_Typ (Tmp_Index)),
                     Context => T);
               end loop;

               T := +Sequence
                 (New_Ignore (Ada_Node => Expr,
                              Prog     => +T),
                  New_Any_Expr
                    (Ada_Node    => Expr,
                     Post        => New_Connection
                       (Op    => EW_Equivalent,
                        Left  => +Pred_Of_Boolean_Term
                          (+New_Result_Ident (EW_Bool_Type)),
                        Right =>
                          Transform_Comparison (Expr, EW_Pred, Params)),
                     Return_Type => EW_Bool_Type,
                     Labels      => Symbol_Sets.Empty_Set));
            end if;
            return T;
         end;
      end Transform_Equal_Of_Update;

      Left      : constant Node_Id := Left_Opnd (Expr);
      Right     : constant Node_Id := Right_Opnd (Expr);
      Left_Type : constant Entity_Id := Etype (Left);
      T         : W_Expr_Id;

   --  Start of processing for Transform_Comparison

   begin

      --  Special case for equality between Booleans in predicates

      if Domain = EW_Pred
        and then Nkind (Expr) = N_Op_Eq
        and then Is_Standard_Boolean_Type (Left_Type)
      then
         declare
            Left_Expr  : constant W_Expr_Id :=
              Transform_Expr
                (Left,
                 EW_Bool_Type,
                 EW_Pred,
                 Params);
            Right_Expr : constant W_Expr_Id :=
              Transform_Expr
                (Right,
                 EW_Bool_Type,
                 EW_Pred,
                 Params);
         begin
            T :=
              New_Connection
                (Domain => EW_Pred,
                 Left   => Left_Expr,
                 Right  => Right_Expr,
                 Op     => EW_Equivalent);
         end;
      elsif Has_Array_Type (Left_Type) then

         --  If Expr is of the form Id = Id'Old'Update (...) and equality is
         --  not redefined on the array type, we can translate it as
         --  (for all Idx in Id'Range =>
         --     Id (Idx) = (if Idx ... then ... else Id'Old (Idx)))

         if Is_Equal_Of_Update (Expr) then
            T := Transform_Equal_Of_Update (Expr, Domain, Params);

         --  Normal translation

         else
            declare
               Left_Expr  : constant W_Expr_Id :=
                 Transform_Expr
                   (Left,
                    (if Domain = EW_Pred then EW_Term else Domain),
                    Params);
               Right_Expr : constant W_Expr_Id :=
                 Transform_Expr
                   (Right,
                    (if Domain = EW_Pred then EW_Term else Domain),
                    Params);

            begin
               if Nkind (Expr) in N_Op_Eq | N_Op_Ne then
                  T := Transform_Array_Equality
                    (Op        => Nkind (Expr),
                     Left      => Left_Expr,
                     Right     => Right_Expr,
                     Left_Type => Left_Type,
                     Domain    => Domain,
                     Ada_Node  => Expr);
               else
                  T := Transform_Array_Comparison
                    (Op        => Nkind (Expr),
                     Left      => Left_Expr,
                     Right     => Right_Expr,
                     Domain    => Domain,
                     Ada_Node  => Expr);
               end if;
            end;
         end if;
      else
         declare
            Op         : constant Node_Kind := Nkind (Expr);
            Right_Type : constant Node_Id := Etype (Right);
            Subdomain  : constant EW_Domain :=
              (if Domain = EW_Pred then EW_Term else Domain);

            BT         : constant W_Type_Id :=
              Base_Why_Type (Left_Type, Right_Type);
            Left_Expr  : W_Expr_Id :=
              Transform_Expr (Left, BT, Subdomain, Params);
            Right_Expr : W_Expr_Id :=
              Transform_Expr (Right, BT, Subdomain, Params);
         begin

            if Is_Record_Type_In_Why (Left_Type) then
               pragma Assert (Op in N_Op_Eq | N_Op_Ne);
               pragma Assert (Root_Retysp (Left_Type) =
                                Root_Retysp (Right_Type));
               pragma Assert (Root_Retysp (Left_Type) =
                                Root_Retysp (Get_Ada_Node (+BT)));

               --  Check that operands are initialized. Even if initialization
               --  checks are introduced for the conversion to BT, we still
               --  need to insert these checks here to ensure initialization of
               --  nested components with relaxed initialization if any.

               Left_Expr :=
                 Insert_Initialization_Check
                   (Left, Get_Ada_Node (+BT), Left_Expr, Domain);
               Right_Expr :=
                 Insert_Initialization_Check
                   (Right, Get_Ada_Node (+BT), Right_Expr, Domain);

               if Is_Class_Wide_Type (Left_Type) then

                  --  Dispatching equality. Translate to:
                  --  let a = to_root left in
                  --  let b = to_root right in
                  --    a.attr_tag = b.attr_tag /\
                  --    __dispatch_eq a b

                  declare
                     Root : constant Entity_Id :=
                       Root_Retysp (Left_Type);
                     Args : constant W_Expr_Array :=
                       (1 => New_Temp_For_Expr
                          (Insert_Simple_Conversion
                               (Ada_Node => Expr,
                                Domain   => Subdomain,
                                Expr     => Left_Expr,
                                To       => Type_Of_Node (Root))),
                        2 => New_Temp_For_Expr
                          (Insert_Simple_Conversion
                               (Ada_Node => Expr,
                                Domain   => Subdomain,
                                Expr     => Right_Expr,
                                To       => Type_Of_Node (Root))));
                  begin
                     T := New_And_Then_Expr
                       (Left   => New_Call
                          (Ada_Node => Expr,
                           Domain   => Subdomain,
                           Name     => Why_Eq,
                           Args     =>
                             (1 => New_Tag_Access
                                  (Domain => Subdomain,
                                   Name   => Args (1),
                                   Ty     => Root),
                              2 => New_Tag_Access
                                (Domain => Subdomain,
                                 Name   => Args (2),
                                 Ty     => Root)),
                           Typ      => EW_Bool_Type),
                        Right  =>
                          New_Call
                            (Ada_Node => Expr,
                             Domain   => Subdomain,
                             Name     =>
                               E_Symb (Root, WNE_Dispatch_Eq),
                             Args     => Args,
                             Typ      => EW_Bool_Type),
                        Domain => Subdomain);

                     T := Binding_For_Temp (Domain  => Subdomain,
                                            Tmp     => Args (1),
                                            Context => T);
                     T := Binding_For_Temp (Domain  => Subdomain,
                                            Tmp     => Args (2),
                                            Context => T);
                  end;
               else
                  T :=
                    New_Call
                      (Ada_Node => Expr,
                       Domain   => Subdomain,
                       Name     =>
                         E_Symb (Get_Ada_Node (+BT), WNE_Bool_Eq),
                       Args     => (1 => Left_Expr,
                                    2 => Right_Expr),
                       Typ      => EW_Bool_Type);
               end if;

               if Domain = EW_Pred then
                  T := New_Comparison
                    (Symbol =>
                       Transform_Compare_Op (Op, EW_Bool_Type, Domain),
                     Left   => T,
                     Right  => New_Literal (Domain => Subdomain,
                                            Value  => EW_True),
                     Domain => Domain);

               elsif Op = N_Op_Ne then
                  T :=
                    New_Call (Domain => Domain,
                              Name   => M_Boolean.Notb,
                              Args   => (1 => T),
                              Typ    => EW_Bool_Type);
               end if;

            elsif Is_Access_Type (Retysp (Left_Type)) then
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Subdomain,
                    Name     =>
                      E_Symb (Get_Ada_Node (+BT), WNE_Bool_Eq),
                    Args     => (1 => Left_Expr,
                                 2 => Right_Expr),
                    Typ      => EW_Bool_Type);

               if Domain = EW_Pred then
                  T := New_Comparison
                    (Symbol =>
                       Transform_Compare_Op (Op, EW_Bool_Type, Domain),
                     Left   => T,
                     Right  => New_Literal (Domain => Subdomain,
                                            Value  => EW_True),
                     Domain => Domain);

               elsif Op = N_Op_Ne then
                  T :=
                    New_Call (Domain => Domain,
                              Name   => M_Boolean.Notb,
                              Args   => (1 => T),
                              Typ    => EW_Bool_Type);
               end if;

            else
               pragma Assert (Has_Scalar_Type (Left_Type));
               T := New_Comparison
                 (Symbol  => Transform_Compare_Op (Op, BT, Domain),
                  Left    => Left_Expr,
                  Right   => Right_Expr,
                  Domain  => Domain);
            end if;
         end;
      end if;

      return T;
   end Transform_Comparison;

   -----------------------------
   -- Transform_Concatenation --
   -----------------------------

   function Transform_Concatenation
     (Left               : W_Expr_Id;
      Right              : W_Expr_Id;
      Left_Type          : Entity_Id;
      Right_Type         : Entity_Id;
      Return_Type        : Entity_Id;
      Is_Component_Left  : Boolean;
      Is_Component_Right : Boolean;
      Domain             : EW_Domain;
      Ada_Node           : Node_Id) return W_Expr_Id
   is
      Init_Wrapper        : constant Boolean :=
        Expr_Has_Relaxed_Init (Ada_Node);
      Left_Expr           : W_Expr_Id := Left;
      Right_Expr          : W_Expr_Id := Right;
      Args_Len            : constant Positive :=
        (if Is_Component_Left then 2 else 3)
        + (if Is_Component_Right then 1 else 3);
      Args                : W_Expr_Array (1 .. Args_Len);
      Arg_Ind             : Positive := 1;
      T                   : W_Expr_Id;
      First_Expr          : W_Expr_Id;
      Low_Type            : Entity_Id;
      Comp_Type           : constant W_Type_Id :=
        EW_Abstract
          (Component_Type (Return_Type),
           Relaxed_Init => Init_Wrapper
           or else Has_Relaxed_Init (Component_Type (Return_Type)));
      Need_Reconstruction : Boolean := True;
      --  If we need to reconstruct the array after the concatenation

      function Build_Last_Expr return W_Expr_Id;
      --  build the expression that yields the value of the 'Last attribute
      --  of the concatenation. It is simply
      --    first + length of left opnd + length of right_opnd - 1
      --  Last is always computed with integer (even when dealing with modular)
      --  in order to be coherent with length which is always an integer.

      ---------------------
      -- Build_Last_Expr --
      ---------------------

      function Build_Last_Expr return W_Expr_Id is
         One_Term : constant W_Expr_Id :=
           New_Discrete_Constant (Value => Uint_1,
                                  Typ   => EW_Int_Type);
         Left_Length : constant W_Expr_Id :=
           (if Is_Component_Left
            then One_Term
            else
               Build_Length_Expr
              (Domain => Domain,
               First => Get_Array_Attr (Domain, Left_Expr, Attribute_First, 1),
               Last => Get_Array_Attr (Domain, Left_Expr, Attribute_Last, 1)));
         Right_Length : constant W_Expr_Id :=
           (if Is_Component_Right
            then One_Term
            else
               Build_Length_Expr
              (Domain => Domain,
               First => Get_Array_Attr
                 (Domain, Right_Expr, Attribute_First, 1),
               Last => Get_Array_Attr
                 (Domain, Right_Expr, Attribute_Last, 1)));
      begin
         return
           +New_Discrete_Substract
           (Domain,
            New_Discrete_Add
              (Domain,
               First_Expr,
               New_Discrete_Add
                 (Domain,
                  Left_Length,
                  Right_Length),
               EW_Int_Type),
            One_Term);
      end Build_Last_Expr;

   --  Start of processing for Transform_Concatenation

   begin
      --  Step 1: introduce temps for left and right

      Left_Expr := New_Temp_For_Expr (Left_Expr);
      Right_Expr := New_Temp_For_Expr (Right_Expr);

      --  Step 2: compute the lower bound of the concatenation
      --  See RM 4.5.3(6-7) for the rules. The test here is taken from
      --  Expand_Concatenate in exp_ch4.adb.

      Low_Type := Ultimate_Ancestor (Return_Type);

      if Is_Constrained (Low_Type) then
         First_Expr := Get_Array_Attr (Domain, Low_Type, Attribute_First, 1);

      elsif Is_Component_Left then
         First_Expr :=
           New_Attribute_Expr
             (Nth_Index_Type (Return_Type, 1),
              Domain, Attribute_First, Body_Params);

      else
         First_Expr := Get_Array_Attr (Domain, Left_Expr, Attribute_First, 1);
      end if;

      --  Step 3: build the actual concatenation expression.
      --  Step 3.1: if Left is empty then concatenate returns Right. If the
      --  length of Left is known statically, return Right.

      if not Is_Component_Left
        and then Is_Static_Array_Type (Left_Type)
        and then Static_Array_Length (Left_Type, 1) = Uint_0
      then
         declare
            Right_First : constant W_Expr_Id :=
              (if Is_Component_Right then
                  New_Attribute_Expr
                 (Nth_Index_Type (Return_Type, 1),
                  Domain,
                  Attribute_First,
                  Body_Params)
               else Get_Array_Attr
                 (Domain, Right_Expr, Attribute_First, 1));
         begin
            if Is_Component_Right then
               T := New_Singleton_Call
                 (Domain,
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Right_Expr,
                                            To     => Comp_Type),
                  Right_First,
                  Type_Of_Node (Ada_Node));
            else
               Need_Reconstruction := False;
               T := Right_Expr;
            end if;
         end;

      --  Step 3.2: Left is not statically empty, do the actual concatenation

      else
         --  We prepare the arguments to the concat call. If one of the sides
         --  is a component, need to possibly convert it to the right type
         --  (think of integer literals, need to convert to Standard__Integer).

         if Is_Component_Left then
            Args (1) := Insert_Simple_Conversion
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Expr     => Left_Expr,
               To       => Comp_Type);
            Args (2) := First_Expr;
            Arg_Ind := 3;
         else
            Add_Array_Arg (Domain, Args, Left_Expr, Arg_Ind);

            --  If we are expecting a partially initialized type, convert Left

            if Init_Wrapper and then not Is_Init_Wrapper_Type (Get_Type (Left))
            then
               Args (1) := New_Call
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Name     => Get_Array_To_Wrapper_Name (Left_Type),
                  Args     => (1 => Args (1)),
                  Typ      => EW_Split (Left_Type, Relaxed_Init => True));
            end if;
         end if;

         if Is_Component_Right then
            Args (Arg_Ind) := Insert_Simple_Conversion (Domain => Domain,
                                                        Expr   => Right_Expr,
                                                        To     => Comp_Type);

            Arg_Ind := Arg_Ind + 1;
         else
            Add_Array_Arg (Domain, Args, Right_Expr, Arg_Ind);

            --  If we are expecting a partially initialized type, convert Right

            if Init_Wrapper
              and then not Is_Init_Wrapper_Type (Get_Type (Right))
            then
               Args (Arg_Ind - 3) := New_Call
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Name     => Get_Array_To_Wrapper_Name (Right_Type),
                  Args     => (1 => Args (Arg_Ind - 3)),
                  Typ      => EW_Split (Left_Type, Relaxed_Init => True));
            end if;
         end if;

         --  We build the call to concat

         T := New_Concat_Call (Domain, Args, Type_Of_Node (Ada_Node),
                               Is_Component_Left  => Is_Component_Left,
                               Is_Component_Right => Is_Component_Right);

         --  Depending on the lower bound of the concat, the object may not be
         --  slided correctly, because the concat operator in Why assumes that
         --  the new low bound is the one of the left opnd. Correct that.

         if not Is_Component_Left
           and then Is_Constrained (Low_Type)
         then
            T :=
              New_Call
                (Domain => Domain,
                 Name   => Get_Array_Theory (Return_Type, Init_Wrapper).Slide,
                 Args   =>
                   (1 => T,
                    2 =>
                      Get_Array_Attr (Domain, Left_Expr, Attribute_First, 1),
                    3 => First_Expr),
                 Typ    => Type_Of_Node (Ada_Node));
         end if;
      end if;

      --  Step 4: the expression T is of the Why array type. We need to convert
      --  it to the type of the concatenation expression. This type is always
      --  unconstrained. Therefore, we need to convert to the unconstrained
      --  representation. This situation also requires a range check.

      pragma Assert (not Is_Constrained (Return_Type));

      if Need_Reconstruction then
         declare
            Target    : constant Entity_Id := Nth_Index_Type (Return_Type, 1);
            Last_Expr : W_Expr_Id := Build_Last_Expr;
         begin
            Last_Expr :=
              Insert_Simple_Conversion
                (Domain         => EW_Prog,
                 Expr           =>
                   (if Domain = EW_Prog then
                           +Do_Range_Check (Ada_Node   => Ada_Node,
                                            Ty         => Target,
                                            W_Expr     => Last_Expr,
                                            Check_Kind => RCK_Range)
                    else Last_Expr),
                 To             => Get_Type (First_Expr));

            T := Array_Convert_From_Base
              (Domain => Domain,
               Ty     => Return_Type,
               Ar     => T,
               First  => First_Expr,
               Last   => Last_Expr);
         end;
      end if;

      --  Step 5: if the Left operand is not static, it may still be a null
      --  array. Generate a conditional for this case.

      if not Is_Component_Left
        and then not Is_Static_Array_Type (Left_Type)
      then
         declare
            Right_First : constant W_Expr_Id :=
              (if Is_Component_Right then
                  New_Attribute_Expr
                 (Nth_Index_Type (Return_Type, 1),
                  Domain,
                  Attribute_First,
                  Body_Params)
               else
                  Get_Array_Attr (Domain, Right_Expr, Attribute_First, 1));
            Right_Last  : constant W_Expr_Id :=
              (if Is_Component_Right then Right_First
               else Get_Array_Attr (Domain, Right_Expr, Attribute_Last, 1));
            Right_Op    : W_Expr_Id :=
              (if Is_Component_Right
               then New_Singleton_Call
                 (Domain,
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Right_Expr,
                                            To     => Comp_Type),
                  Right_First,
                  Type_Of_Node (Ada_Node))
               elsif Is_Static_Array_Type (Right_Type)
               or else (Get_Type_Kind (Get_Type (Right_Expr)) = EW_Split)
               then Right_Expr
               else Array_Convert_To_Base (Domain => Domain,
                                           Ar     => Right_Expr));
            Condition   : constant W_Expr_Id :=
              New_Call
                (Domain   => EW_Pred,
                 Typ      => EW_Bool_Type,
                 Name     => Why_Eq,
                 Args     =>
                   (1 =>
                       Get_Array_Attr (Domain, Left_Expr, Attribute_Length, 1),
                    2 => New_Integer_Constant (Value => Uint_0)));
         begin
            if not Is_Static_Array_Type (Return_Type) then
               Right_Op := Array_Convert_From_Base (Domain => Domain,
                                                    Ty     => Return_Type,
                                                    Ar     => Right_Op,
                                                    First  => Right_First,
                                                    Last   => Right_Last);
            end if;

            T := New_Conditional
              (Domain      => Domain,
               Condition   => Condition,
               Then_Part   => Right_Op,
               Else_Part   => T,
               Typ         => Get_Type (T));
         end;
      end if;

      --  Step 6: bind the introduced names if any, and return

      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Left_Expr,
                             Context => T);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
                             Context => T);
      return T;
   end Transform_Concatenation;

   ---------------------------
   -- Transform_Declaration --
   ---------------------------

   function Transform_Declaration (Decl : Node_Id) return W_Prog_Id is

      function Check_Discr_Of_Subtype (Base, Ent : Entity_Id) return W_Prog_Id;
      --  @param Ent a type entity
      --  @param Base the base type of Ent; Empty if Ent has no base type
      --  @return a program to check that the constraints on the discriminants
      --  of Ent are in fact allowed by Base. Return Void if there is nothing
      --  to check.

      function Check_Itypes_Of_Components (Ent : Entity_Id) return W_Prog_Id;
      --  @param Ent a type entity
      --  @return a program to check that the Itypes introduced for components
      --      of Ent are valid.

      function Check_Discr_Of_Subtype (Base, Ent : Entity_Id) return W_Prog_Id
      is
         R : W_Prog_Id := +Void;
      begin
         if Present (Base)
           and then Present (Stored_Constraint (Ent))
         then
            declare
               Discr : Entity_Id := (if Count_Discriminants (Base) > 0
                                     then First_Discriminant (Base)
                                     else Empty);
               Elmt  : Elmt_Id := First_Elmt (Stored_Constraint (Ent));
            begin
               while Present (Discr) loop
                  declare
                     Value   : constant Node_Id := Node (Elmt);
                     Typ     : constant W_Type_Id :=
                       Base_Why_Type_No_Bool (Node_Id'(Type_Of_Node (Value)));
                     W_Value : constant W_Expr_Id :=
                       +Transform_Expr (Value,
                                        Typ,
                                        EW_Prog,
                                        Body_Params);
                  begin
                     R :=
                       New_Binding
                         (Name    => New_Identifier (Name => "_"),
                          Def     =>
                            +Do_Range_Check (Ada_Node   => Value,
                                             W_Expr     => W_Value,
                                             Ty         => Etype (Discr),
                                             Check_Kind => RCK_Range),
                          Context => +R);
                     Next_Discriminant (Discr);
                     Next_Elmt (Elmt);
                  end;
               end loop;
            end;
         end if;
         return R;
      end Check_Discr_Of_Subtype;

      --------------------------------
      -- Check_Itypes_Of_Components --
      --------------------------------

      function Check_Itypes_Of_Components (Ent : Entity_Id) return W_Prog_Id is
         N      : constant Natural :=
           (if not Is_Constrained (Ent) then Count_Discriminants (Ent) else 0);
         Vars   : W_Identifier_Array (1 .. N);
         Vals   : W_Expr_Array (1 .. N);
         Discr  : Entity_Id :=
           (if N > 0 then First_Discriminant (Ent) else Empty);
         Checks : W_Prog_Id := +Void;
         I      : Positive := 1;
         Rec_Id : constant W_Identifier_Id :=
           New_Temp_Identifier (Base_Name => "rec",
                                Typ       => EW_Abstract (Ent));
         --  Identifier for a record object to be used in predicate checks for
         --  components.
         Prop   : W_Pred_Id := True_Pred;
         --  Assume values of the discriminants of Rec_Id

      begin
         --  For:
         --     type My_Rec (D : T) is record
         --       A : Array_Type (1 .. D);
         --       R : Rec_Type (D);
         --     end record;
         --  Generate:
         --     let d = any T in
         --     let rec = any My_Rec { result.d = d }
         --       pred_A rec ->
         --          check_scalar_range (Array_Type (1 .. D), Array_Type);
         --       pred_R rec ->
         --          check_discr_of_subtype (Rec_Type (D), Rec_Type)
         --  where pred_A and pred_R denote whether components A and R are
         --  present in rec.

         Ada_Ent_To_Why.Push_Scope (Symbol_Table);

         --  For unconstrained types with discriminants, store a value for each
         --  discriminant in the symbol table as discrimiants can appear in
         --  Type constraints of components. Don't do it for constrained type.
         --  Indeed, discriminants of constrained types cannot be used for
         --  new component definitions.

         while Present (Discr) loop
            declare
               Typ : constant W_Type_Id := Type_Of_Node (Discr);
            begin
               Vars (I) := New_Temp_Identifier
                 (Base_Name => Short_Name (Discr),
                  Typ       => Typ);
               Insert_Entity (Discr, Vars (I));

               Vals (I) := +New_Any_Statement
                 (Post        => Compute_Dynamic_Invariant
                    (Expr        => +New_Result_Ident (Typ),
                     Ty          => Etype (Discr),
                     Initialized => True_Term,
                     Params      => Body_Params),
                  Return_Type => Typ);

               --  Assume that Rec_Id has Vars (I) for discriminant Discr

               Prop := +New_And_Then_Expr
                 (Left   => +Prop,
                  Right  => New_Comparison
                    (Symbol => Why_Eq,
                     Left   => Insert_Simple_Conversion
                       (Domain => EW_Pterm,
                        Expr   => New_Ada_Record_Access
                          (Ada_Node => Empty,
                           Name     => +New_Result_Ident (Get_Typ (Rec_Id)),
                           Field    => Discr,
                           Ty       => Ent,
                           Domain   => EW_Term),
                        To     => Typ),
                     Right  => +Vars (I),
                     Domain => EW_Pred),
                  Domain => EW_Pred);
            end;
            I := I + 1;
            Next_Discriminant (Discr);
         end loop;

         --  For each component declared in Ent for the first type, check the
         --  constraints on the introduced Itype if any.

         for Comp of Get_Component_Set (Ent) loop
            if Ekind (Comp) = E_Component
              and then Original_Declaration (Comp) = Ent
              and then Is_Itype (Etype (Comp))
            then
               declare
                  Typ   : constant Entity_Id :=
                    Retysp (Etype (Comp));
                  Base  : constant Entity_Id := Retysp (Etype (Typ));
                  Check : W_Prog_Id := +Void;

               begin
                  --  Check range constraint of array indexes

                  if Has_Array_Type (Typ)
                    and then not Is_Constrained (Base)
                  then
                     declare
                        Index      : Node_Id := First_Index (Typ);
                        Index_Base : Node_Id := First_Index (Base);
                     begin

                        while Present (Index) loop
                           Check := Check_Scalar_Range
                             (Params => Body_Params,
                              N      => Etype (Index),
                              Base   => Etype (Index_Base));

                           Next_Index (Index);
                           Next_Index (Index_Base);
                        end loop;
                     end;

                  --  And discriminants of record / private / concurrent types

                  elsif Count_Discriminants (Typ) > 0
                    and then not Is_Constrained (Base)
                  then
                     Check :=  Check_Discr_Of_Subtype (Base, Typ);
                  end if;

                  --  Only perform checks on a component if the component is
                  --  present in the object.

                  if N > 0 then
                     Check := New_Conditional
                       (Condition => New_Ada_Record_Check_For_Field
                          (Domain => EW_Prog,
                           Name   => +Rec_Id,
                           Field  => Comp,
                           Ty     => Ent),
                        Then_Part => +Check);
                  end if;

                  Checks := Sequence (Check, Checks);
               end;
            end if;
         end loop;

         if Checks /= +Void and then N /= 0 then

            --  Introduce a binding for Rec_Id

            Checks := +New_Typed_Binding
              (Domain   => EW_Prog,
               Name     => Rec_Id,
               Def      => +New_Any_Statement
                 (Post        => Prop,
                  Return_Type => Get_Typ (Rec_Id)),
               Context  => +Checks);

            --  Introduce bindings for the discriminants

            for I in Vars'Range loop
               Checks := +New_Typed_Binding
                 (Domain   => EW_Prog,
                  Name     => Vars (I),
                  Def      => Vals (I),
                  Context  => +Checks);
            end loop;
         end if;

         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

         return Checks;
      end Check_Itypes_Of_Components;

      R : W_Prog_Id := +Void;

   --  Start of processing for Transform_Declaration

   begin
      case Nkind (Decl) is
         when N_Object_Declaration =>
            declare
               Obj      : constant Entity_Id := Defining_Identifier (Decl);
               Obj_Type : constant Entity_Id := Etype (Obj);

               Lvalue   : constant Entity_Id := (if Is_Full_View (Obj)
                                                 then Partial_View (Obj)
                                                 else Obj);
            begin
               --  Non-scalar object declaration should not appear before the
               --  loop invariant in a loop.

               pragma Assert
                 (not Is_In_Loop_Initial_Statements
                    or else (Is_Scalar_Type (Obj_Type)
                               and then Is_Loop_Entity (Obj))
                    or else Is_Actions_Entity (Obj));

               R := Assignment_Of_Obj_Decl (Decl);

               --  Assume dynamic invariant of the object

               if not Is_Partial_View (Obj) then
                  declare
                     Obj_Expr : constant W_Term_Id :=
                       +Transform_Identifier (Expr   => Lvalue,
                                              Ent    => Lvalue,
                                              Domain => EW_Term,
                                              Params => Body_Params);
                  begin
                     R :=
                       Sequence
                         (R,
                          Assume_Dynamic_Invariant
                            (Expr        => Obj_Expr,
                             Ty          => Etype (Lvalue),
                             Initialized => Present (Expression (Decl)),
                             Only_Var    => False));

                     --  Check the type invariant of constants with no
                     --  variable inputs.

                     if Ekind (Obj) = E_Constant
                       and then not Has_Variable_Input (Obj)
                       and then Is_Library_Level_Entity (Obj)
                       and then Invariant_Check_Needed (Obj_Type)
                     then
                        pragma Assert (not Is_Mutable_In_Why (Obj));
                        R :=
                          Sequence
                            (R,
                             New_Invariant_Check
                               (Ada_Node => Decl,
                                Ty       => Obj_Type,
                                W_Expr   => +Obj_Expr));
                     end if;
                  end;
               end if;
            end;

         when N_Subtype_Declaration
            | N_Full_Type_Declaration
         =>
            declare
               Ent  : constant Entity_Id :=
                 Retysp (Unique_Defining_Entity (Decl));

               Base : Entity_Id;
               --  ??? this name is rather unfortunate, because we will assign
               --  "Base" with the "Parent_Type".

            begin
               --  Check for absence of run-time errors when the type
               --  declaration is not simply a renaming of an existing type.
               --  This avoids duplicating checks for every such renaming. Do
               --  not generate checks for actual subtypes as they should be
               --  correct by construction.

               pragma Assert (Entity_In_SPARK (Ent));

               if not Is_Type_Renaming (Decl)
                 and then not Is_Actual_Subtype (Ent)
               then
                  Base := Get_Parent_Type_If_Check_Needed (Decl);

                  if Present (Base) then
                     Base := Retysp (Base);
                  end if;

                  case Ekind (Ent) is
                  when Scalar_Kind =>

                     --  Scalar type declarations can only require checks when
                     --  either their range is non-static, or their Base type
                     --  is not static.

                     if (Present (Base)
                         and then
                           not SPARK_Atree.Is_OK_Static_Range
                             (Get_Range (Base)))
                       or else
                         not SPARK_Atree.Is_OK_Static_Range (Get_Range (Ent))
                     then
                        R := Check_Scalar_Range (Params => Body_Params,
                                                 N      => Ent,
                                                 Base   => Base);
                     end if;

                  when Array_Kind =>
                     declare
                        Index      : Node_Id;
                        Index_Base : Entity_Id;
                        Typ        : constant Node_Id :=
                          Component_Subtype_Indication (Decl);

                     begin
                        --  If the component type of the array has a non-static
                        --  subtype_indication, we generate a check that the
                        --  range_constraint is compatible with the subtype.

                        if Present (Typ)
                          and then Nkind (Typ) = N_Subtype_Indication
                          and then Comes_From_Source (Original_Node (Typ))
                        then
                           R := Sequence
                             (Check_Subtype_Indication
                                (Params   => Body_Params,
                                 N        => Typ,
                                 Sub_Type => Component_Type (Ent)),
                              R);
                        end if;

                        --  For each discrete_subtype_definition that is a
                        --  non-static subtype_indication, we generate a check
                        --  that the range_constraint is compatible with the
                        --  subtype.

                        Index := First_Index (Ent);
                        while Present (Index) loop
                           if Nkind (Index) = N_Subtype_Indication then
                              if Comes_From_Source (Original_Node (Index)) then
                                 R := Sequence
                                   (Check_Subtype_Indication
                                      (Params   => Body_Params,
                                       N        => Index,
                                       Sub_Type => Etype (Index)),
                                    R);
                              end if;
                           end if;

                           Next_Index (Index);
                        end loop;

                        --  For each range_constraint of an array subtype, we
                        --  generate a check that it is compatible with the
                        --  subtype of the corresponding index in the base
                        --  array type.

                        if Present (Base) then
                           Index := First_Index (Ent);
                           Index_Base := First_Index (Base);
                           while Present (Index) loop
                              if Comes_From_Source (Original_Node (Index)) then
                                 R := Sequence
                                   (Check_Scalar_Range
                                      (Params => Body_Params,
                                       N      => Etype (Index),
                                       Base   => Etype (Index_Base)),
                                    R);
                              end if;
                              Next_Index (Index);
                              Next_Index (Index_Base);
                           end loop;
                        end if;
                     end;

                  when E_Record_Type
                     | E_Record_Subtype
                     | Concurrent_Kind
                     | Private_Kind
                  =>
                     --  For each component_definition that is a non-static
                     --  subtype_indication, we generate a check that the
                     --  range_constraint is compatible with the subtype. It is
                     --  not necessary to do that check on discriminants, as
                     --  the type of discriminants are directly subtype_marks,
                     --  not subtype_indications.
                     --  We only check newly declared components as inherited
                     --  components should be checked as part of some ancestor
                     --  type declaration.

                     if Ekind (Ent) in E_Record_Type | E_Record_Subtype then
                        declare
                           Typ : Node_Id;
                        begin
                           for Comp of Get_Component_Set (Ent) loop
                              if Ekind (Comp) = E_Component
                                and then Original_Declaration (Comp) = Ent
                              then
                                 Typ := Subtype_Indication
                                   (Component_Definition
                                      (Enclosing_Declaration (Comp)));

                                 if Present (Typ)
                                   and then Nkind (Typ) = N_Subtype_Indication
                                   and then
                                     Comes_From_Source (Original_Node (Typ))
                                 then
                                    R := Sequence
                                      (Check_Subtype_Indication
                                         (Params   => Body_Params,
                                          N        => Typ,
                                          Sub_Type => Etype (Comp)),
                                       R);
                                 end if;
                              end if;
                           end loop;
                        end;
                     end if;

                     --  We need to check that the new discriminants of the
                     --  subtype fit into the base type.

                     R := Sequence (Check_Discr_Of_Subtype (Base, Ent), R);

                     if Ekind (Ent) in E_Record_Type
                                     | E_Record_Subtype
                                     | Concurrent_Kind
                     then
                        R := Sequence (Check_Itypes_Of_Components (Ent), R);
                     end if;

                  when Class_Wide_Kind =>
                     null;

                  when E_Access_Type
                     | E_Access_Subtype
                  =>
                     null;

                  when others =>
                     Ada.Text_IO.Put_Line
                       ("[Transform_Declaration] ekind ="
                        & Entity_Kind'Image (Ekind (Ent)));
                     raise Not_Implemented;
                  end case;
               end if;

               --  If the type has an invariant, check that there can be no
               --  runtime error in the type invariant. If the type, one of its
               --  ancestors, or one of its components has an invariant, check
               --  that default values of the type and all its subtypes respect
               --  the invariant.

               if Nkind (Decl) = N_Full_Type_Declaration
                 and then Invariant_Check_Needed (Ent)
               then
                  R := Sequence
                    (R,
                     Check_Type_With_Invariants (Params => Body_Params,
                                                 N      => Ent));
               end if;
            end;

         when N_Protected_Type_Declaration =>
            declare
               Ent : constant Entity_Id :=
                 Retysp (Unique_Defining_Entity (Decl));
            begin
               if Entity_In_SPARK (Ent) then
                  R := Sequence (Check_Itypes_Of_Components (Ent), R);
               end if;
            end;

         when N_Pragma =>
            R := Transform_Pragma (Decl, Force => False);

         when N_Raise_xxx_Error
            | N_Raise_Statement
         =>
            R := Transform_Raise (Decl);

         when N_Package_Body | N_Package_Declaration =>

            --  Assume dynamic property of local variables.
            --  This should only be done when the nested package has been
            --  elaborated.
            --  ??? What about local variables of nested packages?

            declare
               E : constant Entity_Id := Unique_Defining_Entity (Decl);
            begin

               if not Is_Generic_Unit (E)
                 and then not Is_Wrapper_Package (E)
                 and then (Nkind (Decl) = N_Package_Body
                           or else No (Package_Body (E)))
               then
                  declare
                     Init_Map : constant Dependency_Maps.Map :=
                       Parse_Initializes (E, Get_Flow_Scope (E));

                  begin
                     for Var of States_And_Objects (E) loop
                        if not Is_Abstract_State (Var)
                          and then Entity_In_SPARK (Var)
                          and then Ada_Ent_To_Why.Has_Element
                            (Symbol_Table, Var)
                        then
                           Assume_Declaration_Of_Entity
                             (E             => Var,
                              Params        => Body_Params,
                              Initialized   =>
                                Init_Map.Contains (Direct_Mapping_Id (Var)),
                              Top_Predicate => True,
                              Context       => R);
                        end if;
                     end loop;
                  end;

                  --  Assume initial condition

                  declare
                     Init_Cond : constant Node_Id :=
                       Get_Pragma (E, Pragma_Initial_Condition);

                  begin
                     if Present (Init_Cond) then
                        declare
                           Expr : constant Node_Id :=
                             Expression (First (Pragma_Argument_Associations
                                         (Init_Cond)));
                        begin
                           R := Sequence
                             (R,
                              New_Assume_Statement
                                (Pred => +Transform_Expr
                                     (Expr, EW_Bool_Type, EW_Pred,
                                      Body_Params)));
                        end;
                     end if;
                  end;
               end if;
            end;

         when others =>
            null;
      end case;

      --  Aspect or representation clause Address may involve computations
      --  that could lead to a RTE. Thus we need to check absence of RTE in
      --  the corresponding expression.
      --  We also check for compatibility of the involved types.

      if Nkind (Decl) in N_Object_Declaration
                       | N_Subprogram_Declaration
      then
         declare
            Expr : Node_Id := Get_Address_Rep_Item (Decl);
         begin
            if Present (Expr) then

               --  We emit a static check that the type of the object is OK for
               --  address clauses.

               if Nkind (Decl) = N_Object_Declaration then
                  Emit_Static_Proof_Result
                    (Decl,
                     VC_UC_No_Holes,
                     Is_Valid_Bitpattern_No_Holes
                       (Etype (Defining_Identifier (Decl))),
                     Current_Subp);
               end if;

               --  Attribute Address is only allowed at the top level of an
               --  Address aspect or attribute definition clause. Skip it to
               --  reach to the underlying name if present.

               if Nkind (Expr) = N_Attribute_Reference
                 and then Get_Attribute_Id (Attribute_Name (Expr))
                   = Attribute_Address
               then
                  if Nkind (Decl) = N_Object_Declaration then
                     Emit_Static_Proof_Result
                       (Expr,
                        VC_UC_No_Holes,
                        Is_Valid_Bitpattern_No_Holes
                          (Etype (Prefix (Expr))),
                        Current_Subp);
                     Emit_Static_Proof_Result
                       (Expr,
                        VC_UC_Same_Size,
                        Types_Have_Same_Known_Esize
                          (Etype (Defining_Identifier (Decl)),
                           Etype (Prefix (Expr))),
                        Current_Subp);
                  end if;
                  Expr := Prefix (Expr);
               end if;

               declare
                  Why_Expr : constant W_Expr_Id :=
                    Transform_Expr (Expr, EW_Prog, Body_Params);
               begin
                  R := +Sequence (New_Ignore (Prog => +Why_Expr), R);
               end;
            end if;
         end;
      end if;

      return +Insert_Cnt_Loc_Label (Decl, +R);
   end Transform_Declaration;

   ----------------------------------
   -- Transform_Declarations_Block --
   ----------------------------------

   function Transform_Declarations_Block (L : List_Id; Core : W_Prog_Id)
      return W_Prog_Id
   is
      Cur_Decl : Node_Id := First (L);
      Result   : W_Statement_Sequence_Id := Void_Sequence;

   begin
      while Present (Cur_Decl) loop
         Sequence_Append (Result, Transform_Declaration (Cur_Decl));
         Next (Cur_Decl);
      end loop;
      Sequence_Append (Result, Core);
      return +Result;
   end Transform_Declarations_Block;

   -------------------------------------
   -- Transform_Declarations_For_Body --
   -------------------------------------

   function Transform_Declarations_For_Body
     (L : List_Id) return W_Prog_Id
   is
      Cur_Decl : Node_Id := First (L);
      Result   : W_Statement_Sequence_Id := Void_Sequence;

   begin
      while Present (Cur_Decl)
        and then Declaration_Is_Associated_To_Parameter (Cur_Decl)
      loop
         Next (Cur_Decl);
      end loop;
      while Present (Cur_Decl) loop
         Sequence_Append (Result, Transform_Declaration (Cur_Decl));
         Next (Cur_Decl);
      end loop;
      return +Result;
   end Transform_Declarations_For_Body;

   ---------------------------------------
   -- Transform_Declarations_For_Params --
   ---------------------------------------

   function Transform_Declarations_For_Params
     (L : List_Id) return W_Prog_Id
   is
      Cur_Decl : Node_Id := First (L);
      Result   : W_Statement_Sequence_Id := Void_Sequence;

   begin
      while Present (Cur_Decl)
        and then Declaration_Is_Associated_To_Parameter (Cur_Decl)
      loop
         Sequence_Append (Result, Transform_Declaration (Cur_Decl));
         Next (Cur_Decl);
      end loop;
      return +Result;
   end Transform_Declarations_For_Params;

   -------------------------------
   -- Transform_Delta_Aggregate --
   -------------------------------

   function Transform_Delta_Aggregate
     (Ada_Node : Node_Id;
      Pref     : Node_Id;
      Aggr     : Node_Id;
      Domain   : EW_Domain;
      Params   : Transformation_Params) return W_Expr_Id
   is
      Pref_Typ : constant Entity_Id := Retysp (Etype (Pref));
      W_Pref   : W_Expr_Id;
      T        : W_Expr_Id;

   begin
      if Is_Record_Type (Pref_Typ) then
         W_Pref := +Transform_Expr (Domain => Domain,
                                    Expr   => Pref,
                                    Params => Params);

         --  Introduce a temporary for the prefix to avoid recomputing it
         --  several times if Pref_Typ has discriminants.

         W_Pref := New_Temp_For_Expr (W_Pref, Has_Discriminants (Pref_Typ));

         --  As discriminants may occur as bounds in types of
         --  discriminant dependent components, store them in the
         --  symbol table.

         declare
            Num_Discrs : constant Natural :=
              Count_Discriminants (Pref_Typ);
            Tmps       : W_Identifier_Array (1 .. Num_Discrs);
            Vals       : W_Expr_Array (1 .. Num_Discrs);
         begin
            Ada_Ent_To_Why.Push_Scope (Symbol_Table);
            if Num_Discrs > 0 then
               declare
                  D : Entity_Id := First_Discriminant (Pref_Typ);
               begin
                  for I in 1 .. Num_Discrs loop
                     Tmps (I) := New_Temp_Identifier
                       (Typ => EW_Abstract (Etype (D)));
                     Vals (I) := New_Ada_Record_Access
                       (Ada_Node => Empty,
                        Domain   => EW_Term,
                        Name     => W_Pref,
                        Field    => D,
                        Ty       => Pref_Typ);

                     Insert_Entity (D, Tmps (I));

                     Next_Discriminant (D);
                  end loop;
                  pragma Assert (No (D));
               end;
            end if;

            T := New_Ada_Record_Update
              (Name     => W_Pref,
               Domain   => Domain,
               Updates  =>
                 Transform_Record_Component_Associations
                   (Domain              => Domain,
                    Typ                 => Pref_Typ,
                    Assocs              =>
                      Component_Associations (Aggr),
                    Params              => Params,
                    In_Delta_Aggregate => True,
                    Init_Wrapper        =>
                      Expr_Has_Relaxed_Init (Pref)));

            --  If we are in the program domain and Pref_Typ has discriminants,
            --  check that selectors are present in the prefix.

            if Domain = EW_Prog and then Has_Discriminants (Pref_Typ) then
               declare
                  Association : Node_Id :=
                    Nlists.First (Component_Associations (Aggr));
                  Choice      : Node_Id;
                  Checks      : W_Statement_Sequence_Id := Void_Sequence;
               begin
                  while Present (Association) loop
                     Choice := First (Choices (Association));

                     while Present (Choice) loop
                        Sequence_Append
                          (Checks,
                           (New_Ignore
                                (Prog => +New_Ada_Record_Access
                                   (Ada_Node => Choice,
                                    Domain   => EW_Prog,
                                    Name     => W_Pref,
                                    Field    => Search_Component_In_Type
                                      (Pref_Typ, Entity (Choice)),
                                    Ty       => Pref_Typ))));
                        Next (Choice);
                     end loop;
                     Next (Association);
                  end loop;
                  T := +Sequence (Ada_Node, +Checks, +T);
               end;
            end if;

            --  If the target type has a direct or inherited
            --  predicate, generate a corresponding check.

            if Domain = EW_Prog
              and then Has_Predicates (Pref_Typ)
            then
               T := +Insert_Predicate_Check (Ada_Node => Ada_Node,
                                             Check_Ty => Pref_Typ,
                                             W_Expr   => +T);
            end if;

            --  Add bindings for discriminants

            for I in 1 .. Num_Discrs loop
               T := New_Binding
                 (Domain  => Domain,
                  Name    => Tmps (I),
                  Def     => Vals (I),
                  Context => T,
                  Typ     => Get_Type (T));
            end loop;
            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

            T := Binding_For_Temp
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Tmp      => W_Pref,
               Context  => T);
         end;

      else
         pragma Assert (Is_Array_Type (Pref_Typ));
         T := Transform_Aggregate
           (Params        => Params,
            Domain        => Domain,
            Expr          => Aggr,
            Update_Prefix => Pref);
      end if;
      return T;
   end Transform_Delta_Aggregate;

   -------------------------------
   -- Transform_Discrete_Choice --
   -------------------------------

   function Transform_Discrete_Choice
     (Choice      : Node_Id;
      Choice_Type : Entity_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
      Is_Range  : constant Boolean := Discrete_Choice_Is_Range (Choice);

      R : W_Expr_Id;
   begin
      if Nkind (Choice) = N_Others_Choice then
         R := New_Literal (Domain => Domain, Value => EW_True);

      --  When the choice denotes a subtype with a static predicate, check the
      --  expression against the predicate values.

      elsif (Nkind (Choice) = N_Subtype_Indication
              or else (Is_Entity_Name (Choice)
                        and then Is_Type (Entity (Choice))))
        and then Has_Predicates (Etype (Choice))
        and then Has_Static_Predicate (Etype (Choice))
      then
         pragma Assert (Is_Discrete_Type (Etype (Choice)));
         R := Transform_Discrete_Choices
                (Static_Discrete_Predicate (Etype (Choice)),
                 Choice_Type,
                 Expr,
                 Domain,
                 Params);

      elsif Is_Range then
         R := Range_Expr (Choice, Expr, Domain, Params);

         --  In programs, we generate a check that the range_constraint of a
         --  subtype_indication is compatible with the given subtype.

         if Domain = EW_Prog then
            pragma Assert (Present (Choice_Type));
            R := +Sequence
              (Check_Scalar_Range (Params => Params,
                                   N      => Choice,
                                   Base   => Choice_Type),
               +R);
         end if;

      else
         R := New_Comparison
           (Symbol => Transform_Compare_Op
              (N_Op_Eq, Base_Why_Type_No_Bool (Choice), Domain),
            Left   => Expr,
            Right  => Transform_Expr
              (Expr          => Choice,
               Expected_Type => Base_Why_Type_No_Bool (Choice),
               Domain        => Subdomain,
               Params        => Params),
            Domain => Domain);

         --  In programs, we generate a check that the non-static value of a
         --  choice belongs to the given subtype.

         if Domain = EW_Prog
           and then (not Is_OK_Static_Expression (Choice)
                     or else not Has_Static_Scalar_Subtype (Choice_Type))
         then
            pragma Assert (Present (Choice_Type));
            R := +Sequence
                   (+New_Ignore (Prog =>
                      Do_Range_Check
                        (Ada_Node => Choice,
                         Ty       => Choice_Type,
                         W_Expr   =>
                           Transform_Expr (Expr          => Choice,
                                           Expected_Type =>
                                           Base_Why_Type_No_Bool (Choice),
                                           Domain        => Subdomain,
                                           Params        => Params),
                         Check_Kind => RCK_Range)),
                    +R);
         end if;
      end if;

      return R;
   end Transform_Discrete_Choice;

   --------------------------------
   -- Transform_Discrete_Choices --
   --------------------------------

   function Transform_Discrete_Choices
     (Choices      : List_Id;
      Choice_Type  : Entity_Id;
      Matched_Expr : W_Expr_Id;
      Cond_Domain  : EW_Domain;
      Params       : Transformation_Params) return W_Expr_Id
   is
      Cur_Choice : Node_Id   := First (Choices);
      C          : W_Expr_Id := New_Literal (Domain => Cond_Domain,
                                             Value  => EW_False);
   begin
      while Present (Cur_Choice) loop
         C := New_Or_Else_Expr
           (C,
            Transform_Discrete_Choice (Choice      => Cur_Choice,
                                       Choice_Type => Choice_Type,
                                       Expr        => Matched_Expr,
                                       Domain      => Cond_Domain,
                                       Params      => Params),
            Cond_Domain);
         Next (Cur_Choice);
      end loop;
      return C;
   end Transform_Discrete_Choices;

   ----------------------------
   -- Transform_Enum_Literal --
   ----------------------------

   function Transform_Enum_Literal
     (Expr   : Node_Id;
      Enum   : Entity_Id;
      Domain : EW_Domain)
      return W_Expr_Id is
   begin
      --  Deal with special cases: True/False for boolean literals

      if Enum = Standard_True then
         return New_Literal (Value => EW_True,
                             Domain => Domain,
                             Ada_Node => Standard_Boolean);
      end if;

      if Enum = Standard_False then
         return New_Literal (Value => EW_False,
                             Domain => Domain,
                             Ada_Node => Standard_Boolean);
      end if;

      --  all other enumeration literals are expressed by integers

      return New_Integer_Constant
               (Ada_Node => Etype (Expr),
                Value    => Enumeration_Pos (Enum));
   end Transform_Enum_Literal;

   --------------------
   -- Transform_Expr --
   --------------------

   function Transform_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id
   is
      Expr_Type    : constant Entity_Id := Retysp (Etype (Expr));
      T            : W_Expr_Id;
      Pretty_Label : Symbol := No_Symbol;
      Local_Params : Transformation_Params := Params;

   begin
      --  We check whether we need to generate a pretty printing label. If we
      --  do, we set the corresponding flag to "False" so that the label is not
      --  printed for subterms.

      if Domain = EW_Pred
        and then Local_Params.Gen_Marker /= GM_None
        and then Is_Terminal_Node (Expr)
      then
         Pretty_Label := New_Sub_VC_Marker (Expr);
         Local_Params.Gen_Marker := GM_None;
      end if;

      --  Expressions that cannot be translated to predicates directly are
      --  translated to (boolean) terms, and compared to "True".

      if Domain = EW_Pred

        --  Boolean connectors and predicate expressions

        and then
          not (Nkind (Expr) in N_And_Then
                             | N_Or_Else
                             | N_In
                             | N_If_Expression
                             | N_Quantified_Expression
                             | N_Case_Expression)

        --  Boolean operators which are not private intrinsinc

        and then
          not (Nkind (Expr) in N_Op_Compare
                             | N_Op_Not
                             | N_Op_And
                             | N_Op_Or
               and then not Is_Private_Intrinsic_Op (Expr))

        --  Boolean literals

        and then
          not (Nkind (Expr) in N_Identifier | N_Expanded_Name
              and then Ekind (Entity (Expr)) = E_Enumeration_Literal
              and then Entity (Expr) in Standard_True | Standard_False)

        --  Calls to predicate functions

        and then
          not (Nkind (Expr) = N_Function_Call
             and then Is_Predicate_Function (Get_Called_Entity (Expr)))
      then
         T := +Pred_Of_Boolean_Term
                 (+Transform_Expr (Expr, EW_Bool_Type, EW_Term, Local_Params));

      --  Optimization: if we have a discrete value that is statically known,
      --  use the static value.

      elsif Domain /= EW_Pred
        and then Is_Discrete_Type (Expr_Type)
        and then Compile_Time_Known_Value (Expr)
      then
         T := New_Discrete_Constant
           (Value => Expr_Value (Expr),
            Typ   => Base_Why_Type_No_Bool (Expr_Type));

       --  Intrinsic operators should be translated as function calls in SPARK
       --  if the intrinsic pragma is located in a part with SPARK_Mode Off.
       --  However, a crash will only occur if the base type on which the
       --  operator applies is private in SPARK. Thus, we only check for this
       --  case here. This may result in SPARK being a little too smart and
       --  knowing the value of opeartors even if their intrinsic pragma
       --  shold not be visible.

      elsif Nkind (Expr) in N_Op and then Is_Private_Intrinsic_Op (Expr) then
         T := Transform_Function_Call (Expr, Domain, Local_Params);
      else
         case Nkind (Expr) is
         when N_Aggregate =>
            declare
               Expr_Type : constant Entity_Id := Type_Of_Node (Expr);
            begin
               if Is_Record_Type (Expr_Type) then
                  pragma Assert (Is_Empty_List (Expressions (Expr)));

                  --  If the type is an empty record in Why (no tag, no field,
                  --  no discriminant), we use the dummy node of the root type
                  --  here.

                  if Count_Why_Top_Level_Fields (Expr_Type) = 0 then
                     return
                       +E_Symb (Root_Retysp (Expr_Type), WNE_Dummy);
                  else
                     declare
                        Init_Wrapper : constant Boolean :=
                          Expr_Has_Relaxed_Init (Expr);
                        Assocs : constant W_Field_Association_Array :=
                          Transform_Record_Component_Associations
                            (Domain,
                             Expr_Type,
                             Component_Associations (Expr),
                             Local_Params,
                             Init_Wrapper => Init_Wrapper);
                        Num_Discrs : constant Natural :=
                          Count_Non_Inherited_Discriminants
                            (Component_Associations (Expr));
                     begin
                        T :=
                          New_Ada_Record_Aggregate
                            (Ada_Node     => Expr,
                             Domain       => Domain,
                             Discr_Assocs => Assocs (1 .. Num_Discrs),
                             Field_Assocs =>
                               Assocs (Num_Discrs + 1 .. Assocs'Last),
                             Ty           => Expr_Type,
                             Init_Wrapper => Init_Wrapper);
                     end;
                  end if;
               else
                  pragma Assert
                    (Is_Array_Type (Expr_Type) or else
                     Is_String_Type (Expr_Type));

                  T := Transform_Aggregate (Params => Local_Params,
                                            Domain => Domain,
                                            Expr   => Expr);
               end if;
            end;

         when N_Extension_Aggregate =>
            declare
               Init_Wrapper : constant Boolean :=
                 Expr_Has_Relaxed_Init (Expr);
               Expr_Type : constant Entity_Id := Type_Of_Node (Expr);
               Assocs    : constant W_Field_Association_Array :=
                 Transform_Record_Component_Associations
                   (Domain,
                    Expr_Type,
                    Component_Associations (Expr),
                    Local_Params,
                    Init_Wrapper => Init_Wrapper);

               --  Check that the derived type does not introduce any
               --  discriminant, which is currently not allowed in SPARK,
               --  and not supported by the current scheme which defined
               --  all discriminant types in the root record type.

               Num_Discrs : constant Natural :=
                 Count_Non_Inherited_Discriminants
                   (Component_Associations (Expr));

               pragma Assert (Num_Discrs = 0);

               --  Use the base type of the ancestor part as intermediate type
               --  to which the ancestor is converted if needed before copying
               --  its fields to the extension aggregate. This takes care
               --  of generating a dummy value for unused components in a
               --  discriminant record, if needed.

               Prefix_Ty : constant Entity_Id :=
                 Retysp (Etype (Ancestor_Part (Expr)));
               Anc_Ty    : constant Entity_Id :=
                 (if Ekind (Prefix_Ty) in E_Record_Subtype |
                                          E_Record_Subtype_With_Private
                  then
                    Retysp (Etype (Prefix_Ty))
                  else
                    Prefix_Ty);

               Anc_Expr : constant W_Expr_Id :=
                 Transform_Expr (Ancestor_Part (Expr),
                                 Type_Of_Node (Anc_Ty),
                                 Domain,
                                 Params);
               Tmp : constant W_Expr_Id := New_Temp_For_Expr (Anc_Expr);
               Anc_Num_Fields : constant Natural :=
                 Count_Why_Regular_Fields (Anc_Ty) - 1;

               --  The number of fields in the ancestor type minus the tag

               Anc_Discr_Expr   : W_Expr_Id;
               Anc_Field_Assocs : W_Field_Association_Array
                                    (1 .. Anc_Num_Fields);

            begin
               Generate_Associations_From_Ancestor
                 (Domain       => Domain,
                  Expr         => Tmp,
                  Anc_Ty       => Anc_Ty,
                  Ty           => Expr_Type,
                  Discr_Expr   => Anc_Discr_Expr,
                  Field_Assocs => Anc_Field_Assocs);
               T :=
                 New_Ada_Record_Aggregate
                   (Domain       => Domain,
                    Discr_Expr   => Anc_Discr_Expr,
                    Field_Assocs => Anc_Field_Assocs & Assocs,
                    Ty           => Expr_Type,
                    Anc_Ty       => Anc_Ty,
                    Init_Wrapper => Init_Wrapper);
               T := Binding_For_Temp (Domain   => Domain,
                                      Tmp      => Tmp,
                                      Context  => T);
            end;

         when N_Slice =>
            T := Transform_Slice (Local_Params, Domain, Expr);

         when N_Integer_Literal =>

            T :=
              New_Integer_Constant
                (Ada_Node => Expr,
                 Value    => Intval (Expr));

         when N_Real_Literal =>

            declare
               Rty : constant Entity_Id := Retysp (Etype (Expr));
            begin

               --  Literals of fixed-point type are directly translated into
               --  the integer that represents them in the corresponding
               --  fixed-point type.

               if Is_Fixed_Point_Type (Rty) then
                  T := New_Fixed_Constant
                    (Ada_Node => Expr,
                     Value    => Corresponding_Integer_Value (Expr),
                     Typ      => Base_Why_Type (Rty));

                  --  It can happen that the literal is a universal real which
                  --  is converted into a fixed point type, we then simply
                  --  return a real constant.

               elsif Is_Universal_Numeric_Type (Rty) then
                  T := New_Real_Constant (Ada_Node => Expr,
                                          Value    => Realval (Expr));

               else
                  T := New_Float_Constant
                    (Ada_Node => Expr,
                     Value    => Realval (Expr),
                     Typ      =>
                       (if Has_Single_Precision_Floating_Point_Type (Rty)
                        then
                           EW_Float_32_Type
                        elsif Has_Double_Precision_Floating_Point_Type (Rty)
                        then
                           EW_Float_64_Type
                        else raise Program_Error));
               end if;
            end;

         when N_Character_Literal =>

            T :=
              New_Integer_Constant (Ada_Node => Expr,
                                    Value    => Char_Literal_Value (Expr));

            --  Deal with identifiers:
            --  * Enumeration literals: deal with special cases True and
            --    False, otherwise such literals are just constants
            --  * local variables are always references
            --  * global constants are logics in Why
            --  * global mutable variables are references
            --  * loop parameters are always mutable, and of type int

         when N_String_Literal =>
            declare
               M  : W_Module_Id := E_Module (Expr);
               Id : W_Identifier_Id;
            begin
               if M = Why_Empty then
                  Transform_String_Literal (Local_Params, Expr);
                  M := E_Module (Expr);
               end if;
               Id :=
                 New_Identifier
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Module   => M,
                    Symb     => NID (Lower_Case_First (Img (Get_Name (M)))),
                    Typ      => New_Abstract_Base_Type (Type_Of_Node (Expr)));
               T := New_Call (Ada_Node => Expr,
                              Domain   => Domain,
                              Name     => Id,
                              Args     => (1 .. 1 => +Void),
                              Typ      => Get_Typ (Id));
            end;

         when N_Identifier
            | N_Expanded_Name
         =>
            T := Transform_Identifier (Local_Params, Expr,
                                       Entity (Expr),
                                       Domain);

         when N_Op_Compare =>

            T := Transform_Comparison
              (Expr   => Expr,
               Domain => Domain,
               Params => Local_Params);

         when N_Op_Minus =>  --  unary minus
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
               Typ   : constant W_Type_Id := Base_Why_Type (Right);

               Minus_Ident : constant W_Identifier_Id :=
                 (if Typ = EW_Int_Type then
                    Int_Unary_Minus
                  elsif Why_Type_Is_BitVector (Typ) then
                    MF_BVs (Typ).Neg
                  elsif Why_Type_Is_Fixed (Typ) then
                    Fixed_Unary_Minus
                  else MF_Floats (Typ).Unary_Minus);

               Right_Rep : constant W_Expr_Id :=
                 Transform_Expr (Right, Typ, Domain, Local_Params);

            begin
               if Has_Modular_Integer_Type (Expr_Type)
                 and then Non_Binary_Modulus (Expr_Type)
               then
                  T := Transform_Non_Binary_Modular_Operation
                    (Ada_Node   => Expr,
                     Ada_Type   => Expr_Type,
                     Domain     => Domain,
                     Op         => N_Op_Minus,
                     Right_Opnd => Right_Rep,
                     Rep_Type   => Typ,
                     Modulus    => Modulus (Expr_Type));
               else
                  T :=
                    New_Call
                      (Domain   => Domain,
                       Ada_Node => Expr,
                       Name     => Minus_Ident,
                       Args     =>
                         (1 => Right_Rep),
                       Typ       => Typ);
                  T := Apply_Modulus (N_Op_Minus, Expr_Type, T, Domain);
               end if;

               if Domain = EW_Prog
                 and then Has_No_Wrap_Around_Annotation (Expr_Type)
               then
                  declare
                     Check : constant W_Prog_Id :=
                       Check_No_Wrap_Around_Modular_Operation
                         (Ada_Node   => Expr,
                          Ada_Type   => Expr_Type,
                          Op         => N_Op_Minus,
                          Right_Opnd => Right_Rep,
                          Rep_Type   => Typ,
                          Modulus    => Modulus (Expr_Type));
                  begin
                     T := +Sequence (Check, +T);
                  end;
               end if;
            end;

         when N_Op_Plus =>  --  unary plus
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               T := Transform_Expr
                 (Right, Base_Why_Type (Right), Domain, Local_Params);
            end;

         when N_Op_Abs =>
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
               Typ   : constant W_Type_Id := Base_Why_Type (Right);

               Right_Rep : constant W_Expr_Id :=
                 Transform_Expr (Right, Typ, Domain, Local_Params);
            begin
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => New_Abs (Typ),
                    Args     => (1 => Right_Rep),
                    Typ     => Typ);
            end;

         when N_Op_Add
            | N_Op_Subtract
         =>
            declare
               Left       : constant Node_Id := Left_Opnd (Expr);
               Right      : constant Node_Id := Right_Opnd (Expr);
               Base       : constant W_Type_Id := Base_Why_Type (Left, Right);
               Left_Expr  : constant W_Expr_Id :=
                 Transform_Expr (Left,
                                 Base,
                                 Domain,
                                 Local_Params);
               Right_Expr : constant W_Expr_Id :=
                 Transform_Expr (Right,
                                 Base,
                                 Domain,
                                 Local_Params);
            begin
               T := New_Binary_Op_Expr
                 (Op          => Nkind (Expr),
                  Left        => Left_Expr,
                  Right       => Right_Expr,
                  Left_Type   => Etype (Left),
                  Right_Type  => Etype (Right),
                  Return_Type => Expr_Type,
                  Domain      => Domain,
                  Ada_Node    => Expr);
            end;

         when N_Op_Multiply
            | N_Op_Divide
         =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               L_Type, R_Type : W_Type_Id;
               L_Why, R_Why : W_Expr_Id;
            begin
               if Has_Fixed_Point_Type (Etype (Left))
                 and then Has_Fixed_Point_Type (Etype (Right))
               then
                  --  Multiplication/division between fixed-point types
                  --  requires the creation of a specific module.

                  Create_Fixed_Point_Mult_Div_Theory_If_Needed
                    (Current_File => Params.File,
                     Typ_Left     => Etype (Left),
                     Typ_Right    => Etype (Right),
                     Typ_Result   => Expr_Type,
                     Expr         => Expr);

                  L_Type := Base_Why_Type (Etype (Left));
                  R_Type := Base_Why_Type (Etype (Right));

               elsif Has_Fixed_Point_Type (Etype (Left)) then
                  L_Type := Base_Why_Type (Etype (Left));
                  R_Type := EW_Int_Type;

               elsif Nkind (Expr) = N_Op_Multiply
                 and then Has_Fixed_Point_Type (Etype (Right))
               then
                  L_Type := EW_Int_Type;
                  R_Type := Base_Why_Type (Etype (Right));

               else
                  L_Type := Base_Why_Type (Left, Right);
                  R_Type := Base_Why_Type (Left, Right);
               end if;

               L_Why :=
                 Transform_Expr (Left,
                                 L_Type,
                                 Domain,
                                 Local_Params);
               R_Why :=
                 Transform_Expr (Right,
                                 R_Type,
                                 Domain,
                                 Local_Params);

               T := New_Binary_Op_Expr
                 (Op          => Nkind (Expr),
                  Left        => L_Why,
                  Right       => R_Why,
                  Left_Type   => Etype (Left),
                  Right_Type  => Etype (Right),
                  Return_Type => Expr_Type,
                  Domain      => Domain,
                  Ada_Node    => Expr);
            end;

         when N_Op_Rem
            | N_Op_Mod
         =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Base  : constant W_Type_Id := Base_Why_Type (Left, Right);
            begin

               T := New_Binary_Op_Expr
                 (Op          => Nkind (Expr),
                  Left        => Transform_Expr (Left,
                    Base,
                    Domain,
                    Local_Params),
                  Right       => Transform_Expr (Right,
                    Base,
                    Domain,
                    Local_Params),
                  Left_Type   => Etype (Left),
                  Right_Type  => Etype (Right),
                  Return_Type => Expr_Type,
                  Domain      => Domain,
                  Ada_Node    => Expr);
            end;

         when N_Op_Expon =>

            --  Optimization: try to inline the exponentiation when possible.
            --  This optimization is primarly intended for floating-points,
            --  hence we only inline the exponentiation for power between -3
            --  and 3. Indeed, the Ada RM does not guarantee that beyond those
            --  values the exponentiation is equal to a specific factorisation
            --  (float multiplication is commutative but not associative).
            --  Since the code is mostly generic and the inlining seems to
            --  help the provers, the optimization is not limited to
            --  floating-points exponentiation.

            declare
               Left      : constant Node_Id := Left_Opnd (Expr);
               Right     : constant Node_Id := Right_Opnd (Expr);
               W_Right   : constant W_Expr_Id :=
                 Transform_Expr (Right,
                                 EW_Int_Type,
                                 Domain,
                                 Local_Params);
               Base_Type : constant W_Type_Id := Base_Why_Type (Left);
               W_Left    : constant W_Expr_Id :=
                 Transform_Expr (Left,
                                 Base_Type,
                                 Domain,
                                 Local_Params);
               Left_Type : constant Entity_Id := Etype (Left);

               One : constant W_Expr_Id :=
                 (if Has_Modular_Integer_Type (Left_Type) then
                       New_Modular_Constant (Ada_Node => Expr,
                                             Value    => Uint_1,
                                             Typ      => Base_Type)
                  elsif Has_Signed_Integer_Type (Left_Type) then
                       New_Integer_Constant (Ada_Node => Expr,
                                             Value => Uint_1)
                  elsif Has_Floating_Point_Type (Left_Type) then
                       +MF_Floats (Base_Type).One
                  else raise Program_Error);

               function Square (X : W_Expr_Id; T : Entity_Id)
                                return W_Expr_Id is
                 (New_Binary_Op_Expr (Op          => N_Op_Multiply,
                                      Left        => X,
                                      Right       => X,
                                      Left_Type   => T,
                                      Right_Type  => T,
                                      Return_Type => Expr_Type,
                                      Domain      => Domain,
                                      Ada_Node    => Expr));

               function Cube (X : W_Expr_Id; T : Entity_Id) return W_Expr_Id is
                 (New_Binary_Op_Expr (Op          => N_Op_Multiply,
                                      Left        => X,
                                      Right       => Square (X, T),
                                      Left_Type   => T,
                                      Right_Type  => T,
                                      Return_Type => Expr_Type,
                                      Domain      => Domain,
                                      Ada_Node    => Expr));

               function Inv (X : W_Expr_Id; T : Entity_Id) return W_Expr_Id;
               --  Return 1 / X
               --  Insert a division check depending on the domain

               function Inv (X : W_Expr_Id; T : Entity_Id) return W_Expr_Id
               is
                  E : constant W_Expr_Id :=
                    New_Binary_Op_Expr (Op          => N_Op_Divide,
                                        Left        => One,
                                        Right       => X,
                                        Left_Type   => T,
                                        Right_Type  => T,
                                        Return_Type => Expr_Type,
                                        Domain      => Domain);

               begin
                  if Domain = EW_Prog then
                     declare
                        Check : constant W_Prog_Id :=
                          New_Located_Assert
                            (Ada_Node => Expr,
                             Pred     =>
                               +New_Comparison
                               (Why_Neq, X,
                                +MF_Floats (Get_Type (X)).Plus_Zero,
                                EW_Term),
                             Reason   => VC_Division_Check,
                             Kind     => EW_Assert);
                     begin
                        return +Sequence (Check, +E);
                     end;
                  else
                     return E;
                  end if;
               end Inv;

            begin
               --  Translate powers of 2 on modular types as shifts. If the
               --  modulus is not a power of two, this cannot be done as the
               --  power computation must not wrap-around on the rep bitvector
               --  type.

               if Has_Modular_Integer_Type (Left_Type)
                 and then not Non_Binary_Modulus (Left_Type)
                 and then Compile_Time_Known_Value (Left)
                 and then Expr_Value (Left) = Uint_2
               then
                  declare
                     Typ  : constant W_Type_Id := Base_Why_Type (Left_Type);
                     Expo : constant W_Expr_Id := New_Temp_For_Expr (W_Right);
                  begin
                     T := New_Call
                       (Ada_Node => Expr,
                        Domain   => Domain,
                        Name     => MF_BVs (Typ).Lsl,
                        Args     =>
                          (1 => New_Modular_Constant (Value => Uint_1,
                                                      Typ   => Typ),
                           2 => Insert_Simple_Conversion
                             (Domain => Domain,
                              Expr   => Expo,
                              To     => Typ)),
                        Typ      => Typ);

                     --  If the exponent does not fit in the modular type,
                     --  return 0.

                     T := New_Conditional
                       (Domain      => Domain,
                        Condition   =>
                          New_Comparison
                            (Symbol => Int_Infix_Lt,
                             Left   => Insert_Simple_Conversion
                               (Domain   => EW_Term,
                                Expr     => Expo,
                                To       => EW_Int_Type),
                             Right  => +MF_BVs (Typ).Two_Power_Size,
                             Domain => EW_Pred),
                        Then_Part   => T,
                        Else_Part   => New_Modular_Constant (Value => Uint_0,
                                                             Typ   => Typ),
                        Typ         => Typ);

                     --  Apply the modulus if it is smaller than the modulus
                     --  of the rep bitvector type.

                     T := Apply_Modulus (Nkind (Expr), Left_Type, T, Domain);
                     T := Binding_For_Temp
                       (Domain => Domain, Tmp => Expo, Context => T);
                  end;

               --  Static exponentiation up to 3 are expended into equivalent
               --  multiplications.

               elsif Nkind (Right) = N_Integer_Literal then
                  declare
                     Exp : constant Uint := Intval (Right);
                  begin
                     if UI_Eq (Exp, Uint_0) then
                        if Domain = EW_Prog then
                           T := +Sequence (New_Ignore (Prog => +W_Left),
                                           +One);
                        else
                           T := One;
                        end if;
                     elsif UI_Eq (Exp, Uint_1) then
                        T := W_Left;
                     elsif UI_Eq (Exp, Uint_2) then
                        T := Square (W_Left, Left_Type);
                     elsif UI_Eq (Exp, Uint_3) then
                        T := Cube (W_Left, Left_Type);
                     elsif UI_Eq (Exp, UI_Negate (Uint_1)) then
                        T := Inv (W_Left, Left_Type);
                     elsif UI_Eq (Exp, UI_Negate (Uint_2)) then
                        T := Inv (Square (W_Left, Left_Type), Left_Type);
                     elsif UI_Eq (Exp, UI_Negate (Uint_3)) then
                        T := Inv (Cube (W_Left, Left_Type), Left_Type);
                     else
                        T := New_Binary_Op_Expr
                          (Op          => N_Op_Expon,
                           Left        => W_Left,
                           Right       => W_Right,
                           Left_Type   => Left_Type,
                           Right_Type  => Etype (Right),
                           Return_Type => Expr_Type,
                           Domain      => Domain,
                           Ada_Node    => Expr);
                     end if;
                  end;
               else
                  T := New_Binary_Op_Expr
                    (Op          => N_Op_Expon,
                     Left        => W_Left,
                     Right       => W_Right,
                     Left_Type   => Etype (Left),
                     Right_Type  => Etype (Right),
                     Return_Type => Expr_Type,
                     Domain      => Domain,
                     Ada_Node    => Expr);
               end if;
            end;

         when N_Op_Not =>
            if Has_Array_Type (Etype (Right_Opnd (Expr))) then
               declare
                  Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
               begin
                  T := Transform_Array_Negation
                    (Right       => Transform_Expr
                       (Right_Opnd (Expr), Subdomain, Params),
                     Right_Type  => Etype (Right_Opnd (Expr)),
                     Domain      => Domain,
                     Ada_Node    => Expr,
                     Do_Check    => Domain = EW_Prog);
               end;

            elsif Is_Modular_Integer_Type (Expr_Type) then
               declare
                  Base : constant W_Type_Id := Base_Why_Type (Expr_Type);
               begin
                  T := New_Call (Ada_Node => Expr,
                                 Domain   => Domain,
                                 Name     => MF_BVs (Base).BW_Not,
                                 Args     => (1 => Transform_Expr
                                                     (Right_Opnd (Expr),
                                                      Base,
                                                      Domain,
                                                      Local_Params)),
                                 Typ      => Base);
               end;

            else
               declare
                  Right : constant W_Expr_Id :=
                    Transform_Expr
                      (Right_Opnd (Expr),
                       EW_Bool_Type,
                       Domain,
                       Local_Params);
               begin
                  if Domain = EW_Term then
                     T :=
                       New_Call
                         (Ada_Node => Expr,
                          Domain   => Domain,
                          Name     => M_Boolean.Notb,
                          Args     => (1 => Right),
                          Typ      => EW_Bool_Type);
                  else
                     T :=
                       New_Not
                         (Right  => Right,
                          Domain => Domain);
                  end if;
               end;
            end if;

         when N_Op_And
            | N_Op_Or
            | N_Op_Xor
         =>
            if Has_Array_Type (Etype (Left_Opnd (Expr))) then
               declare
                  Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
               begin

                  T := Transform_Array_Logical_Op
                    (Op          => Nkind (Expr),
                     Left        =>
                       Transform_Expr (Left_Opnd (Expr), Subdomain, Params),
                     Right       =>
                       Transform_Expr (Right_Opnd (Expr), Subdomain, Params),
                     Left_Type   => Etype (Left_Opnd (Expr)),
                     Domain      => Domain,
                     Ada_Node    => Expr,
                     Do_Check    => Domain = EW_Prog);
               end;
            else
               declare
                  Op    : constant Node_Kind := Nkind (Expr);
                  Base  : constant W_Type_Id :=
                    (if Is_Boolean_Type (Expr_Type) then EW_Bool_Type
                     else Base_Why_Type (Expr_Type));
                  Left  : constant W_Expr_Id :=
                    Transform_Expr (Left_Opnd (Expr),
                                    Base,
                                    Domain,
                                    Local_Params);
                  Right : constant W_Expr_Id :=
                    Transform_Expr (Right_Opnd (Expr),
                                    Base,
                                    Domain,
                                    Local_Params);
               begin
                  if Op = N_Op_And then
                     T := New_And_Expr (Left, Right, Domain, Base);
                  else
                     if Op = N_Op_Or then
                        T := New_Or_Expr (Left, Right, Domain, Base);
                     else
                        T := New_Xor_Expr (Left, Right, Domain, Base);
                     end if;

                     --  If we're dealing with modulars of non binary modulus
                     --  or and xor might overflow : we need to take the
                     --  modulo of the result.

                     if Has_Modular_Integer_Type (Expr_Type) and then
                       Non_Binary_Modulus (Expr_Type)
                     then
                        T := Apply_Modulus
                          (Op     => Op,
                           E      => Expr_Type,
                           T      => T,
                           Domain => Domain);
                     end if;
                  end if;
               end;
            end if;

         when N_Short_Circuit =>
            Short_Circuit : declare

               function New_Short_Circuit_Expr
                 (Left, Right : W_Expr_Id;
                  Domain      : EW_Domain) return W_Expr_Id;
               --  Dispatch over functions to create a short-circuit Why expr

               ----------------------------
               -- New_Short_Circuit_Expr --
               ----------------------------

               function New_Short_Circuit_Expr
                 (Left, Right : W_Expr_Id;
                  Domain      : EW_Domain) return W_Expr_Id is
               begin
                  if Nkind (Expr) = N_And_Then then
                     return New_And_Then_Expr (Left, Right, Domain);
                  else
                     return New_Or_Else_Expr (Left, Right, Domain);
                  end if;
               end New_Short_Circuit_Expr;

               Left : constant W_Expr_Id :=
                 Transform_Expr (Left_Opnd (Expr),
                                 EW_Bool_Type,
                                 Domain,
                                 Local_Params);
               Right : W_Expr_Id;

            --  Start of processing for Short_Circuit

            begin
               Ada_Ent_To_Why.Push_Scope (Symbol_Table);

               if Present (Actions (Expr)) then
                  Transform_Actions_Preparation (Actions (Expr));
               end if;

               Right := Transform_Expr (Right_Opnd (Expr),
                                        EW_Bool_Type,
                                        Domain,
                                        Local_Params);

               --  Possibly warn on an unreachable right branch

               if Domain = EW_Prog then
                  Right :=
                    Warn_On_Dead_Branch (Right_Opnd (Expr), Right,
                                         Local_Params.Phase);
               end if;

               if Present (Actions (Expr)) then
                  Right := Transform_Actions (Actions (Expr),
                                              Right,
                                              Domain,
                                              Local_Params);
               end if;

               T := New_Short_Circuit_Expr (Left   => Left,
                                            Right  => Right,
                                            Domain => Domain);

               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
            end Short_Circuit;

         when N_Op_Concat =>
            T := Transform_Concatenation
              (Left               =>
                  Transform_Expr (Left_Opnd (Expr), Domain, Params),
               Right              =>
                  Transform_Expr (Right_Opnd (Expr), Domain, Params),
               Left_Type          => Etype (Left_Opnd (Expr)),
               Right_Type         => Etype (Right_Opnd (Expr)),
               Return_Type        => Etype (Expr),
               Is_Component_Left  => Is_Component_Left_Opnd (Expr),
               Is_Component_Right => Is_Component_Right_Opnd (Expr),
               Domain             => Domain,
               Ada_Node           => Expr);

         when N_Membership_Test =>
            T := Transform_Membership_Expression (Local_Params, Domain, Expr);

         when N_Quantified_Expression =>
            T := Transform_Quantified_Expression (Expr, Domain, Local_Params);

         when N_If_Expression =>
            declare
               Cond        : constant Node_Id := First (Expressions (Expr));
               Then_Part   : constant Node_Id := Next (Cond);
               Else_Part   : constant Node_Id := Next (Then_Part);
               Cond_Domain : constant EW_Domain :=
                 (if Domain = EW_Term then EW_Pred else Domain);
               Phase       : constant Transformation_Phase :=
                 Local_Params.Phase;
               Then_Expr, Else_Expr : W_Expr_Id;
               Condition   : W_Expr_Id;

            begin
               Then_Expr :=
                 Transform_Expr_With_Actions (Then_Part,
                                              Then_Actions (Expr),
                                              Expected_Type,
                                              Domain,
                                              Local_Params);

               --  Possibly warn on an unreachable then-branch

               if Domain = EW_Prog then
                  Then_Expr :=
                    Warn_On_Dead_Branch (Then_Part, Then_Expr, Phase);
               end if;

               Else_Expr :=
                 Transform_Expr_With_Actions (Else_Part,
                                              Else_Actions (Expr),
                                              Expected_Type,
                                              Domain,
                                              Local_Params);

               --  Do not warn on an unreachable branch "else True" whether it
               --  comes from source or it was generated by the frontend.

               if Nkind (Else_Part) in N_Expanded_Name |  N_Identifier
                 and then Entity (Else_Part) = Standard_True
               then
                  null;

               --  Otherwise possibly warn on an unreachable else-branch

               elsif Domain = EW_Prog then
                  Else_Expr :=
                    Warn_On_Dead_Branch (Else_Part, Else_Expr, Phase);
               end if;

               Local_Params.Gen_Marker := GM_None;
               Condition :=
                 +Transform_Expr (Cond,
                                  EW_Bool_Type,
                                  Cond_Domain,
                                  Local_Params);

               T :=
                  New_Conditional
                     (Ada_Node  => Expr,
                      Domain    => Domain,
                      Condition => Condition,
                      Then_Part => Then_Expr,
                      Else_Part => Else_Expr,
                      Typ       => Get_Type (Then_Expr));
            end;

         when N_Qualified_Expression
            | N_Type_Conversion
         =>
            --  When converting between elementary types, only require that the
            --  converted expression is translated into a value of the expected
            --  base type. Necessary checks, rounding and conversions will
            --  be introduced at the end of Transform_Expr below. Fixed-point
            --  types are special, because the base type __fixed really
            --  represents a different base for every fixed-point type, so use
            --  full conversion to the expected type in that case. Types with
            --  predicates are also treated specially, so that the type with
            --  predicate is explicitly the target of the conversion, to avoid
            --  having it being skipped.

            if Is_Elementary_Type (Expr_Type)
              and then not Has_Fixed_Point_Type (Expr_Type)
              and then not Has_Predicates (Expr_Type)
            then
               T := Transform_Expr (Expression (Expr),
                                    Base_Why_Type (Expr_Type),
                                    Domain,
                                    Local_Params);

            --  In other cases, require that the converted expression
            --  is translated into a value of the type of the conversion.

            --  When converting to a discriminant record or an array, this
            --  ensures that the proper target type can be retrieved from
            --  the current node, to call the right checking function.

            else
               --  For array conversions, if target and source types have
               --  different component type, we may need to generate an
               --  appropriate conversion theory.
               --  Also generate the theory for the reverse conversion as it
               --  may be needed if Expr is a left value.

               if Has_Array_Type (Etype (Expr)) then
                  declare
                     Target_Typ      : constant Entity_Id :=
                       Retysp (Etype (Expr));
                     Target_Comp_Typ : constant Entity_Id :=
                       Retysp (Component_Type (Target_Typ));
                     Source_Typ      : constant Entity_Id :=
                       Retysp (Etype (Expression (Expr)));
                     Source_Comp_Typ : constant Entity_Id :=
                       Retysp (Component_Type (Source_Typ));
                  begin
                     if Target_Comp_Typ /= Source_Comp_Typ then
                        Create_Array_Conversion_Theory_If_Needed
                          (Current_File => Local_Params.File,
                           From         => Source_Typ,
                           To           => Target_Typ);
                        Create_Array_Conversion_Theory_If_Needed
                          (Current_File => Local_Params.File,
                           From         => Target_Typ,
                           To           => Source_Typ);
                     end if;
                  end;

               elsif Has_Fixed_Point_Type (Expr_Type)
                 and then Has_Fixed_Point_Type (Etype (Expression (Expr)))
               then
                  declare
                     From_Small : constant Ureal :=
                       Small_Value (Retysp (Etype (Expression (Expr))));
                     To_Small   : constant Ureal :=
                       Small_Value (Expr_Type);
                  begin
                     if From_Small /= To_Small then
                        Create_Fixed_Point_Mult_Div_Theory_If_Needed
                          (Current_File => Params.File,
                           Typ_Left     => Etype (Expression (Expr)),
                           Typ_Right    => Standard_Integer,
                           Typ_Result   => Expr_Type,
                           Expr         => Expr);
                     end if;
                  end;
               end if;

               --  For qualification over arrays, we need to check that the
               --  bounds are correct, and not slide the array to match the
               --  bound. Add the conversion manually so that the proper
               --  parameter can be used to get the proper checks.

               if Nkind (Expr) = N_Qualified_Expression
                 and then Has_Array_Type (Etype (Expr))
                 and then Is_Constrained (Etype (Expr))
                 and then Domain = EW_Prog
               then
                  T := Transform_Expr (Expression (Expr),
                                       Type_Of_Node (Expression (Expr)),
                                       Domain,
                                       Local_Params);

                  --  Insert the conversion with In_Qualif set to True so that
                  --  we do not generate length checks but index checks.

                  T := Insert_Array_Conversion
                    (Domain     => EW_Prog,
                     Ada_Node   => Expr,
                     Expr       => T,
                     To         => Type_Of_Node (Expr),
                     Need_Check =>
                       Check_Needed_On_Conversion
                         (From => Etype (Expression (Expr)),
                          To   => Etype (Expr)),
                     Is_Qualif  => True);

               else
                  T := Transform_Expr (Expression (Expr),
                                       Type_Of_Node (Expr),
                                       Domain,
                                       Local_Params);
               end if;
            end if;

            --  Invariant checks are introduced explicitly as they need only be
            --  performed on actual type conversions (and not view
            --  conversions).

            if Domain = EW_Prog
              and then Invariant_Check_Needed (Expr_Type)
            then
               T := +Insert_Invariant_Check (Expr, Expr_Type, +T);
            end if;

         when N_Unchecked_Type_Conversion =>

            --  Source unchecked type conversion nodes were rewritten as such
            --  by SPARK_Rewrite.Rewrite_Call, keeping the original call to an
            --  instance of Unchecked_Conversion as the Original_Node of the
            --  new N_Unchecked_Type_Conversion node, and marking the node as
            --  coming from source. We translate this original node to Why.

            if Comes_From_Source (Expr) then
               T := Transform_Expr (Original_Node (Expr),
                                    Expected_Type,
                                    Domain,
                                    Local_Params);

            --  Compiler-generated unchecked type conversions may have been
            --  rewritten into the converted expression in SPARK_Rewrite, when
            --  needed to propagate the Do_Range_Check flag to the converted
            --  expression. In any case, they are transparent for Why with our
            --  translation.

            else
               T := Transform_Expr (Expression (Expr),
                                    Expected_Type,
                                    Domain,
                                    Local_Params);
            end if;

         when N_Function_Call =>
            if Is_Simple_Shift_Or_Rotate (Get_Called_Entity (Expr)) then
               T := Transform_Shift_Or_Rotate_Call
                      (Expr, Domain, Local_Params);
            elsif Is_Predicate_Function (Get_Called_Entity (Expr)) then

               --  Calls to predicate functions are ignored. Inherited
               --  predicates are handled by other means. This is needed to
               --  be able to handle inherited predicates which are not
               --  visible in SPARK.

               return New_Literal (Value => EW_True, Domain => Domain);
            elsif Has_Pledge_Annotation (Get_Called_Entity (Expr)) then
               declare
                  Fst_Act : constant Node_Id := First_Actual (Expr);
                  Brower  : constant Entity_Id :=
                    (if Nkind (Fst_Act) in N_Expanded_Name | N_Identifier
                     then Entity (Fst_Act)
                     else Entity (Prefix (Fst_Act)));
               begin
                  T := Transform_Pledge_Call
                    (Brower,
                     Next_Actual (First_Actual (Expr)),
                     Domain,
                     Local_Params);
               end;
            else
               T := Transform_Function_Call (Expr, Domain, Local_Params);
            end if;

         when N_Indexed_Component
            | N_Selected_Component
            | N_Explicit_Dereference
         =>
            T := One_Level_Access (Expr,
                                   Transform_Expr
                                     (Prefix (Expr), Domain, Local_Params),
                                   Domain,
                                   Local_Params);

         --  Nothing is done on the rhs (expr) when assigning null to
         --  the lhs object. However, the lhs should be updated and the
         --  field is_null_pointer in the why representation is set to True

         when N_Null =>
            T := +E_Symb (Etype (Expr), WNE_Null_Pointer);

         when N_Attribute_Reference =>
            T := Transform_Attr (Expr, Domain, Local_Params, Expected_Type);

         when N_Case_Expression =>
            T := Case_Expr_Of_Ada_Node
                   (Expr,
                    Expected_Type,
                    Domain,
                    Local_Params);

         when N_Expression_With_Actions =>

            --  We must be in a declare expression, so Actions (Expr)
            --  should only contain renamings which we ignore and object
            --  declarations which should be translated as let bindings.

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);

            declare
               Max_Vars : constant Natural :=
                 Natural (Nlists.List_Length (Actions (Expr)));
               Temps    : W_Identifier_Array (1 .. Max_Vars);
               Values   : W_Expr_Array (1 .. Max_Vars);
               Decl     : Node_Id := Nlists.First (Actions (Expr));
               Count    : Natural := 0;

            begin
               while Present (Decl) loop
                  case Nkind (Decl) is

                     --  Create an item for the declared object, bind it
                     --  to the Ada entity in the Symbol_Table and store the
                     --  definition in Values to create the binding afterward.

                     when N_Object_Declaration =>
                        declare
                           Name  : constant Entity_Id :=
                             Defining_Identifier (Decl);
                           Item  : constant Item_Type :=
                             Mk_Item_Of_Entity (Name, Local => True);
                           pragma Assert (Item.Kind = Regular);
                           Value : constant W_Expr_Id :=
                             Transform_Expr
                               (Expr          => Expression (Decl),
                                Domain        => Domain,
                                Params        => Params,
                                Expected_Type =>
                                  Get_Typ (Item.Main.B_Name));
                        begin
                           Count := Count + 1;
                           Values (Count) := Value;
                           Temps (Count) := Item.Main.B_Name;

                           Ada_Ent_To_Why.Insert (Symbol_Table, Name, Item);
                        end;
                     when N_Ignored_In_SPARK
                        | N_Subtype_Declaration
                        | N_Full_Type_Declaration
                        =>
                        null;
                     when others =>
                        raise Program_Error;
                  end case;
                  Nlists.Next (Decl);
               end loop;

               T := Transform_Expr
                 (Expr          => Expression (Expr),
                  Domain        => Domain,
                  Params        => Params,
                  Expected_Type => Expected_Type);

               --  Add check for absence of memory leaks at end of scope

               if Domain = EW_Prog then
                  T := +Sequence
                    (Left     => Check_No_Memory_Leaks_At_End_Of_Scope
                       (Decls => Actions (Expr)),
                     Right    => +T,
                     Ada_Node => Expr);
               end if;

               --  Add bindings for declared constants

               for I in reverse 1 .. Count loop
                  T := New_Binding
                    (Ada_Node => Expr,
                     Domain   => Domain,
                     Name     => Temps (I),
                     Def      => Values (I),
                     Context  => T,
                     Typ      => Get_Type (T));
               end loop;

               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
            end;

         when N_Allocator =>

            --  For the evaluation of an initialized allocator, the evaluation
            --  of the qualified_expression is performed first.

            --  For The evaluation of an uninitialized allocator,
            --  the elaboration of the subtype_indication is performed first.

            --  see ARM 4.8 $6/3

            declare
               Func_New_Uninitialized_Name : W_Identifier_Id;
               Func_New_Initialized_Name   : W_Identifier_Id;

               Call     : W_Expr_Id;
               New_Expr : constant Node_Id := Expression (Expr);
               Exp_Ty   : constant Node_Id := Retysp (Etype (Expr));
               Des_Ty   : constant Entity_Id :=
                 Directly_Designated_Type (Exp_Ty);

            begin
               --  Uninitialized allocator
               --  Subtype indication are rewritten by the frontend into the
               --  corresponding Itype, so we only expect subtype names here.
               --  Attribute references like Type'Base are also rewritten, but
               --  it feels safer to not rely on this rewriting.

               if Is_Entity_Name (New_Expr)
                 and then Is_Type (Entity (New_Expr))
               then
                  Func_New_Uninitialized_Name :=
                    E_Symb (Etype (Expr), WNE_Uninit_Allocator);

                  Call := New_Call
                    (Ada_Node => Expr,
                     Domain   => Domain,
                     Name     => Func_New_Uninitialized_Name,
                     Args     => (1 => +Void),
                     Typ      => Get_Typ (Func_New_Uninitialized_Name));

                  --  Construct the value for the uninitialized data. We
                  --  generate:
                  --  Constr_ty.default_checks;
                  --  let alloc = __new_uninitialized_allocator () in
                  --  let value = to_des_ty
                  --    (any constr_ty ensures
                  --     { Constr_ty.default_initial_condition result /\
                  --       Constr_ty.dynamic_invariant result }) in
                  --  assume { alloc.rec__value = value };
                  --  alloc

                  declare
                     Call_Ty   : constant W_Type_Id :=
                       Get_Typ (Func_New_Uninitialized_Name);
                     Constr_Ty : constant Entity_Id := Entity (New_Expr);
                     pragma Assert
                       (Default_Initialization (Constr_Ty) in
                          Full_Default_Initialization |
                          No_Possible_Initialization);

                     Value_Id   : constant W_Identifier_Id :=
                       New_Temp_Identifier
                         (Base_Name => "value",
                          Typ       => EW_Abstract
                            (Des_Ty,
                             Relaxed_Init => Has_Relaxed_Init (Des_Ty)));
                     Alloc_Id   : constant W_Identifier_Id :=
                       New_Temp_Identifier
                         (Base_Name => "alloc",
                          Typ       => Call_Ty);
                     Res_Id     : constant W_Identifier_Id :=
                       +New_Result_Ident
                       (Typ => EW_Abstract
                          (Constr_Ty, Has_Relaxed_Init (Constr_Ty)));
                     Pred       : constant W_Pred_Id :=
                       +New_And_Expr
                       (Left   => +Compute_Default_Init
                          (Expr   => +Res_Id,
                           Ty     => Constr_Ty,
                           Params => Body_Params),
                        Right  => +Compute_Dynamic_Invariant
                          (Expr             => +Res_Id,
                           Ty               => Constr_Ty,
                           Params           => Body_Params,
                           --  Uninitialized allocators are only allowed if
                           --  the type defines full default init.
                           Initialized      => True_Term,
                           --  Also assume bounds / discriminants
                           Only_Var         => False_Term),
                        Domain => EW_Pred);
                     Value_Expr : constant W_Expr_Id :=
                       New_Any_Expr
                         (Post        => Pred,
                          Labels      => Symbol_Sets.Empty_Set,
                          Return_Type => Get_Typ (Res_Id));
                  begin
                     pragma Assert
                       (if Is_Composite_Type (Constr_Ty)
                        then Is_Constrained (Constr_Ty)
                        or else Has_Defaulted_Discriminants (Constr_Ty));

                     Call := New_Binding
                       (Name    => New_Identifier (Name => "_"),
                        Domain  => EW_Prog,
                        Def     =>
                          +Compute_Default_Check
                          (Ada_Node => Expr,
                           Ty       => Constr_Ty,
                           Params   => Body_Params),
                        Context => New_Binding
                          (Name    => Alloc_Id,
                           Domain  => EW_Prog,
                           Def     => Call,
                           Context => New_Binding
                             (Name    => Value_Id,
                              Domain  => Domain,
                              Def     => Insert_Checked_Conversion
                                (Ada_Node => Expr,
                                 Domain   => Domain,
                                 Expr     => Value_Expr,
                                 To       => Get_Typ (Value_Id)),
                              Context => +Sequence
                                (Left  => New_Assume_Statement
                                     (Pred => +New_Comparison
                                          (Symbol => Why_Eq,
                                           Left   => New_Pointer_Value_Access
                                             (Ada_Node => Expr,
                                              E        => Exp_Ty,
                                              Name     => +Alloc_Id,
                                              Domain   => EW_Term),
                                           Right  => +Value_Id,
                                           Domain => EW_Pred)),
                                 Right => +Alloc_Id),
                              Typ     => Call_Ty),
                           Typ     => Call_Ty),
                        Typ     => Call_Ty);
                  end;

               --  Initialized allocator

               --  ??? 6/3 If the designated type of the type of the allocator

               else
                  pragma Assert (Nkind (New_Expr) = N_Qualified_Expression);

                  Func_New_Initialized_Name :=
                    E_Symb (Etype (Expr), WNE_Init_Allocator);

                  declare
                     Value_Expr : W_Expr_Id := Transform_Expr
                       (Expr          => New_Expr,
                        Expected_Type => Type_Of_Node (Etype (New_Expr)),
                        Domain        => Domain,
                        Params        => Local_Params);

                  begin
                     --  Update the tag attribute if Des_Ty is a specific type

                     if Is_Tagged_Type (Des_Ty) then
                        Value_Expr := New_Tag_Update
                          (Domain => EW_Term,
                           Name   => Value_Expr,
                           Ty     => Des_Ty);
                     end if;

                     Call := New_Call
                       (Name     => +Func_New_Initialized_Name,
                        Domain   => Domain,
                        Args     => (1 => Value_Expr),
                        Typ      => Get_Typ (Func_New_Initialized_Name));
                  end;

               end if;

               --  If the allocator type has a direct or inherited
               --  predicate, generate a corresponding check.

               if Domain = EW_Prog
                 and then Has_Predicates (Exp_Ty)
               then
                  Call := +Insert_Predicate_Check (Ada_Node => Expr,
                                                   Check_Ty => Exp_Ty,
                                                   W_Expr   => +Call);
               end if;

               T := +Call;
            end;

         when N_Raise_Expression =>

            --  Using raise expressions inside preconditions to change the
            --  reported error is a common pattern used in the standard
            --  library. To support it, we translate raise expressions
            --  occurring in preconditions as False.
            --  NB. Cases where such a translation would be incorrect are
            --  detected in marking.

            if Raise_Occurs_In_Pre (Expr) then
               T := New_Literal (Value => EW_False, Domain => Domain);
            else
               T := Why_Default_Value (Domain, Etype (Expr));
               if Domain = EW_Prog then
                  T := +Sequence
                    (Left  => Transform_Raise (Expr),
                     Right => +T);
               end if;
            end if;

         when N_Delta_Aggregate =>
            T := Transform_Delta_Aggregate
              (Ada_Node => Expr,
               Pref     => Expression (Expr),
               Aggr     => Expr,
               Domain   => Domain,
               Params   => Params);

         when others =>
            Ada.Text_IO.Put_Line ("[Transform_Expr] kind ="
                                  & Node_Kind'Image (Nkind (Expr)));
            raise Not_Implemented;
         end case;
      end if;

      --  We now have the translation of the Ada expression in [T], pending
      --  checks and conversion. We now do the wrapping up to insert all those
      --  if needed.

      --  This label will be used for pretty printing the expression

      if Pretty_Label /= No_Symbol then
         declare
            Label_Set : Symbol_Set := Symbol_Sets.To_Set (Pretty_Label);
         begin
            if Params.Gen_Marker = GM_All then
               Label_Set.Include (New_Located_Label (Expr, Left_Most => True));
            end if;
            T :=
              New_Label (Labels => Label_Set,
                         Def => T,
                         Domain => Domain,
                         Typ    => Get_Type (T));
         end;
      end if;

      --  Insert an overflow check if flag Do_Overflow_Check is set. No
      --  conversion should be needed, as overflow checks are only set on
      --  intermediate expressions, whose transformation into Why should
      --  always have type "int" or "real". We start by checking that Expr has
      --  a kind on which we can call Do_Overflow_Check, otherwise there is
      --  nothing to do.

      --  Note that N_Type_Conversions *may* have a Do_Overflow_Check flag, but
      --  they are actually for range checks and are checked elsewhere. See the
      --  documentation of sinfo.ads.

      if Domain = EW_Prog
        and then Nkind (Expr) in N_Attribute_Reference |
                                 N_Case_Expression     |
                                 N_If_Expression       |
                                 N_Op
        and then Do_Overflow_Check (Expr)
      then
         --  Depending on the current mode for integer overflow checks, the
         --  operation is either done in the base type (Strict mode), or in
         --  Long_Long_Integer (Minimized mode) if needed, or in arbitrary
         --  precision if needed (Eliminated mode). A check may only be
         --  generated in the Strict and Minimized modes, and the type
         --  used for the bounds is the base type in the first case, and
         --  Long_Long_Integer in the second case (which is its own base type).

         --  Use Sem.Scope_Suppress which takes into account the default from
         --  switches and configuration pragma files as defined in
         --  Opt.Suppress_Options, as well as possible configuration pragmas
         --  in the main unit, as done in SPARK_Definition.Mark_Pragma.

         if Is_Signed_Integer_Type (Expr_Type) then
            declare
               Mode : Overflow_Mode_Type;
            begin
               case Params.Phase is
                  when Generate_VCs_For_Body =>
                     Mode := Sem.Scope_Suppress.Overflow_Mode_General;
                  when Generate_VCs_For_Assertion =>
                     Mode := Sem.Scope_Suppress.Overflow_Mode_Assertions;
                  when others =>
                     raise Program_Error;
               end case;

               case Mode is
                  when Strict =>
                     T := Insert_Overflow_Check (Expr, T, Expr_Type,
                                                 Is_Float => False);
                  when Minimized =>
                     T := Insert_Overflow_Check (Expr, T, Standard_Integer_64,
                                                 Is_Float => False);
                  when Eliminated =>
                     null;
                  when Not_Set =>
                     raise Program_Error;
               end case;
            end;

         elsif Is_Floating_Point_Type (Expr_Type) then
            declare
               Tlo : constant Node_Id := Type_Low_Bound  (Expr_Type);
               Thi : constant Node_Id := Type_High_Bound (Expr_Type);
               Lov : Ureal;
               Hiv : Ureal;
               Lo  : Ureal;
               Hi  : Ureal;
               OK  : Boolean;
               True_Check_Inserted : Boolean := False;

            begin
              --  We can only remove the check if we can compute the expected
              --  bounds of the Range_Type now.

               if Compile_Time_Known_Value (Tlo)
                 and then Compile_Time_Known_Value (Thi)
               then
                  Lov := Expr_Value_R (Tlo);
                  Hiv := Expr_Value_R (Thi);

                  Determine_Range_R
                    (Expr, OK, Lo, Hi, Assume_Valid => True);

                  if OK then

                     --  If definitely in range, generate a check always true
                     --  for the overflow check. When gnat2why directly handles
                     --  check messages, a message could be generated instead
                     --  here.

                     --  Note in the test below that we assume that the range
                     --  is not OK if a bound of the range is equal to that
                     --  of the type. That's not the most precise check, but
                     --  we do it for the same reasons as those presented in
                     --  Checks.Enable_Overflow_Check in the same case.

                     if Lo > Lov and then Hi < Hiv then
                        True_Check_Inserted := True;
                        Emit_Always_True_Range_Check (Expr, RCK_FP_Overflow);
                     end if;
                  end if;
               end if;

               if not True_Check_Inserted then
                  T := Insert_Overflow_Check (Expr, T, Expr_Type,
                                              Is_Float => True);
               end if;
            end;

         --  Not a signed integer type or a floating-point type. Always perform
         --  the overflow check.

         else
            T := Insert_Overflow_Check (Expr, T, Expr_Type, Is_Float => False);
         end if;
      end if;

      --  Convert the expression to the expected type, if needed. This is
      --  intertwined with inserting range checks, and Insert_Conversion does
      --  both. This is because range checks need to be done on the Why "int"
      --  type, so they may trigger a conversion, or if a conversion is already
      --  needed, must be done on the "right side" of the conversion.
      --  Note that Insert_Conversion is smart enough to not insert any
      --  conversion when it's not needed.

      --  A range check is needed only in programs (Domain EW_Prog), and on
      --  nodes that have the range check flag. For type conversions, the
      --  Do_Overflow_Check actually means that a range check is needed,
      --  instead of an overflow check (see sinfo.ads and the discussion of
      --  range checks and overflow checks there). Because range checks are
      --  determined by looking at the parent node, in that special case we go
      --  one step down for the Range_Check_Node.

      --  In predicate domain, only the Boolean type is used, no conversion is
      --  needed.

      if Domain in EW_Pred then
         null;
      else
         T := Insert_Checked_Conversion (Ada_Node => Expr,
                                         Domain   => Domain,
                                         Expr     => T,
                                         To       => Expected_Type);
      end if;

      return T;
   end Transform_Expr;

   function Transform_Expr
     (Expr    : Node_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id
   is
      Expected_Type : W_Type_Id := Why_Empty;

   begin
      --  For record fields, use the type of the field access (that is, the
      --  type of the field in the Retyps of the record type) to avoid
      --  conversions.
      --  Note that this type may depend on discriminants, so it is in general
      --  a bad idea to try to convert to such a type. Converting from it
      --  should be OK though as it is never in split form.

      if Nkind (Expr) = N_Selected_Component then
         declare
            Field : constant Entity_Id := Entity (Selector_Name (Expr));
            Ty    : constant Entity_Id :=
              Retysp (Etype (Prefix (Expr)));
         begin
            Expected_Type :=
              (if Is_Part_Of_Protected_Object (Field)
               then EW_Abstract
                 (Etype (Field),
                  Relaxed_Init => Expr_Has_Relaxed_Init (Expr))
               else EW_Abstract
                 (Etype (Search_Component_In_Type (Ty, Field)),
                  Relaxed_Init => Expr_Has_Relaxed_Init (Expr)));
            --  If the component may have relaxed initialization, use the
            --  associated wrapper type.
         end;

      else
         Expected_Type := Type_Of_Node (Expr);
      end if;

      --  Set error node so that bugbox information will be correct

      Current_Error_Node := Expr;

      return Transform_Expr (Expr, Expected_Type, Domain, Params);
   end Transform_Expr;

   ---------------------------------
   -- Transform_Expr_With_Actions --
   ---------------------------------

   function Transform_Expr_With_Actions
     (Expr          : Node_Id;
      Actions       : List_Id;
      Expected_Type : W_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id
   is
      T : W_Expr_Id;

   begin
      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      if Present (Actions) then
         Transform_Actions_Preparation (Actions);
      end if;

      T := Transform_Expr (Expr,
                           Expected_Type,
                           Domain,
                           Params);

      if Present (Actions) then
         T := Transform_Actions (Actions, T, Domain, Params);
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      return T;
   end Transform_Expr_With_Actions;

   function Transform_Expr_With_Actions
     (Expr    : Node_Id;
      Actions : List_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id is
   begin
      return Transform_Expr_With_Actions
        (Expr, Actions, Type_Of_Node (Expr), Domain, Params);
   end Transform_Expr_With_Actions;

   -----------------------------
   -- Transform_Function_Call --
   -----------------------------

   function Transform_Function_Call
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
      Context  : Ref_Context;
      Store    : constant W_Statement_Sequence_Unchecked_Id :=
        New_Unchecked_Statement_Sequence;
      T        : W_Expr_Id;
      Subp     : constant Entity_Id := Get_Called_Entity (Expr);

      Selector : constant Selection_Kind :=
         --  When the call is dispatching, use the Dispatch variant of
         --  the program function, which has the appropriate contract.

        (if Nkind (Expr) = N_Function_Call
         and then Present (Controlling_Argument (Expr))
         then Dispatch

         --  When the call has visibility over the refined postcondition of the
         --  subprogram, use the Refine variant of the program function, which
         --  has the appropriate refined contract.

         elsif Entity_Body_In_SPARK (Subp)
           and then Has_Contracts (Subp, Pragma_Refined_Post)
           and then Has_Visibility_On_Refined (Expr, Subp)
         then
            Refine

         --  Otherwise use the Standard variant of the program function
         --  (defined outside any namespace, directly in the module for
         --  the program function).

         else Why.Inter.Standard);

      Tag_Expr : constant W_Expr_Id :=
        (if Selector = Dispatch then
            Transform_Expr
              (Expr   => Controlling_Argument (Expr),
               Domain => Term_Domain (Domain),
               Params => Params)
         else Why_Empty);
      Tag_Arg  : constant W_Expr_Array :=
        (if Selector = Dispatch then
           (1 => New_Tag_Access
                (Domain => Term_Domain (Domain),
                 Name   => Tag_Expr,
                 Ty     => Get_Ada_Node (+Get_Type (Tag_Expr))))
         else (1 .. 0 => <>));
      --  Calls to dispatching function need the dispatching tag as an
      --  additional argument.

      Args     : constant W_Expr_Array :=
        Tag_Arg &
        Compute_Call_Args (Expr, Domain, Context, Store, Params);

      Why_Name : W_Identifier_Id;

   begin

      --  Hardcoded function calls are transformed in a specific function

      if Is_Hardcoded_Entity (Subp) then
         T := Transform_Hardcoded_Function_Call
           (Subp, Args, Domain, Expr);
         return T;
      end if;

      Why_Name :=
        W_Identifier_Id
          (Transform_Identifier (Params   => Params,
                                 Expr     => Expr,
                                 Ent      => Subp,
                                 Domain   => Domain,
                                 Selector => Selector));

      if Domain in EW_Term | EW_Pred then
         T := New_Function_Call
           (Ada_Node => Expr,
            Domain   => Domain,
            Subp     => Subp,
            Selector => Selector,
            Name     => Why_Name,
            Args     => Args,
            Typ      => Get_Typ (Why_Name));
      elsif Why_Subp_Has_Precondition (Subp, Selector) then
         T := New_VC_Call
           (Ada_Node => Expr,
            Name     => Why_Name,
            Progs    => Args,
            Reason   => VC_Precondition,
            Domain   => Domain,
            Typ      => Get_Typ (Why_Name));
      else
         T := New_Call
           (Name     => Why_Name,
            Args     => Args,
            Ada_Node => Expr,
            Domain   => Domain,
            Typ      => Get_Typ (Why_Name));
      end if;

      --  There are no tag checks on dispatching equality. Instead, the
      --  operator returns False. Take care of this special case by
      --  constructing the expression:
      --  if x.tag = y.tag then f x y else false

      if Selector = Dispatch and then Is_Rewritten_Op_Eq (Expr) then
         declare
            Tags   : W_Expr_Array (1 .. 2);
            Tag_Id : Positive := 1;
            procedure One_Param (Formal : Entity_Id; Actual : Node_Id);
            --  Compute the tag expression for each parameter and store it
            --  inside Tags.

            ---------------
            -- One_Param --
            ---------------

            procedure One_Param (Formal : Entity_Id; Actual : Node_Id) is
               pragma Unreferenced (Formal);
               pragma Assert (Is_Controlling_Actual (Actual));
               Tmp : constant W_Expr_Id :=
                 Transform_Expr (Actual, EW_Term, Params);
            begin
               Tags (Tag_Id) :=
                 New_Tag_Access
                   (Ada_Node => Actual,
                    Domain   => EW_Term,
                    Name     => Tmp,
                    Ty       => Get_Ada_Node (+Get_Type (Tmp)));
               Tag_Id := Tag_Id + 1;
            end One_Param;

            procedure Iterate_Call is new Iterate_Call_Parameters (One_Param);

         begin
            Iterate_Call (Expr);

            T := New_Conditional
              (Ada_Node  => Expr,
               Domain    => Domain,
               Condition => New_Comparison
                 (Symbol => Why_Eq,
                  Left   => Tags (1),
                  Right  => Tags (2),
                  Domain => Domain),
               Then_Part => T,
               Else_Part => New_Literal (Value => EW_False, Domain => Domain),
               Typ       => EW_Bool_Type);
         end;
      end if;

      if Domain = EW_Prog then

         --  Insert invariant check if needed

         if Subp_Needs_Invariant_Checks (Subp) then
            T := +Sequence
              (+New_VC_Call
                 (Ada_Node => Expr,
                  Name     => E_Symb (Subp, WNE_Check_Invariants_On_Call),
                  Progs    => Args,
                  Reason   => VC_Invariant_Check,
                  Domain   => Domain,
                  Typ      => EW_Unit_Type),
               +T);
         end if;

         --  Insert tag check if needed

         if Selector = Dispatch and then not Is_Rewritten_Op_Eq (Expr) then
            T := +Sequence (Compute_Tag_Check (Expr, Params),
                            +T);
         end if;

      --  If -gnatd_f is used, and if for some reason we have not generated a
      --  contract for Subp and Subp is called in the logic domain, notify the
      --  user that the contract will not be available.

      elsif Debug.Debug_Flag_Underscore_F
        and then Domain in EW_Pred | EW_Term
        and then not Entity_In_Ext_Axioms (Subp)
      then
         declare
            Has_Explicit_Contracts : constant Boolean :=
              Has_Contracts (Subp, Pragma_Postcondition)
              or else Has_Contracts (Subp, Pragma_Contract_Cases);
            Has_Implicit_Contracts : constant Boolean :=
              Type_Needs_Dynamic_Invariant (Etype (Subp));
            Is_Expression_Function : constant Boolean :=
              Is_Expression_Function_Or_Completion (Subp)
              and then Entity_Body_Compatible_With_SPARK (Subp);
            Subp_Non_Returning     : constant Boolean :=
              Is_Potentially_Nonreturning (Subp);
            Subp_Recursive         : constant Boolean :=
              Is_Recursive (Subp);
         begin

            if Subp_Non_Returning
              and then (Has_Implicit_Contracts or else Has_Explicit_Contracts)
            then
               declare
                  String_For_Implicit : constant String :=
                    (if Has_Explicit_Contracts then ""
                     else "implicit ");
               begin
                  Error_Msg_NE
                    ("info: ?" & String_For_Implicit
                     & "function contract not available for "
                     & "proof (& might not return)", Expr, Subp);
               end;
            end if;

            if Subp_Recursive
              and then Subp_Non_Returning
              and then Is_Expression_Function
            then
               Error_Msg_NE
                 ("info: ?expression function body not available for "
                  & "proof (& might not return)", Expr, Subp);
            end if;
         end;
      end if;

      --  Volatile functions cannot have side-effects in SPARK, but translation
      --  of a call to a volatile function may introduce references for
      --  parameters of a volatile type. Insert these references here.

      if Has_Pragma_Volatile_Function (Subp) then
         if Context.Length = 0 then
            return T;
         else
            return +Insert_Ref_Context (Expr, +T, Context, Store);
         end if;

      --  SPARK function cannot have side-effects. Except for volatile
      --  functions, this also means that no references should be
      --  introduced for the call.

      else
         pragma Assert (Context.Length = 0);
      end if;

      return T;
   end Transform_Function_Call;

   --------------------------
   -- Transform_Identifier --
   --------------------------

   function Transform_Identifier
     (Params   : Transformation_Params;
      Expr     : Node_Id;
      Ent      : Entity_Id;
      Domain   : EW_Domain;
      Selector : Selection_Kind := Why.Inter.Standard) return W_Expr_Id
   is
      C          : constant Ada_Ent_To_Why.Cursor :=
        Ada_Ent_To_Why.Find (Symbol_Table, Ent);
      T          : W_Expr_Id;
      Need_Deref : Boolean := False;
      --  Whether dereference need to be applied

      Init_Id    : Opt_Id;
      --  Identifier for intialization flag if any

   begin
      --  The special cases of this function are:
      --  * parameters, whose names are stored in Params.Name_Map (these can
      --    also be refs)
      --    ??? Params has no Name_Map component
      --  * enumeration literals (we have a separate function)
      --  * ids of Standard.ASCII (transform to integer)
      --  * quantified variables (use local name instead of global name)
      --  * fields of protected objects

      if Ada_Ent_To_Why.Has_Element (C) then
         declare
            E : constant Item_Type := Ada_Ent_To_Why.Element (C);
         begin
            Init_Id := E.Init;

            --  If E is a function and Domain is Prog, use the program specific
            --  identifier instead.

            case E.Kind is
               when Func =>
                  if Domain = EW_Prog then
                     T := +E.For_Prog.B_Name;
                  else
                     T := +E.For_Logic.B_Name;
                  end if;

               when Regular
                  | Concurrent_Self
               =>
                  T := +E.Main.B_Name;
                  Need_Deref := E.Main.Mutable;

               when UCArray =>
                  T := +E.Content.B_Name;
                  Need_Deref := E.Content.Mutable;

               when DRecord =>
                  T := Record_From_Split_Form (E, Params.Ref_Allowed);

                  --  Havoc the references of Ent for volatiles with
                  --  Async_Writers.

                  if Has_Async_Writers (Direct_Mapping_Id (Ent))
                    and then Domain = EW_Prog
                  then
                     pragma Assert (Is_Mutable_In_Why (Ent));
                     pragma Assert (Params.Ref_Allowed);

                     --  Assume dynamic invariant of the object after havoc

                     declare
                        Dyn_Prop : constant W_Pred_Id :=
                          Compute_Dynamic_Invariant (Expr   => +T,
                                                     Ty     => E.Typ,
                                                     Params => Params);
                     begin
                        if Dyn_Prop /= True_Pred then
                           T := +Sequence
                             (New_Assume_Statement (Pred => Dyn_Prop),
                              +T);
                        end if;
                     end;

                     --  Havoc the reference for fields

                     if E.Fields.Present then
                        pragma Assert (E.Fields.Binder.Mutable);

                        T := +Sequence
                          (New_Havoc_Call (E.Fields.Binder.B_Name),
                           +T);
                     end if;

                     --  If the object is not constrained then also havoc the
                     --  reference for discriminants.

                     if E.Discrs.Present and then E.Discrs.Binder.Mutable then
                        pragma Assert (E.Constr.Present);

                        declare
                           Havoc_Discr      : constant W_Prog_Id :=
                             New_Havoc_Call (E.Discrs.Binder.B_Name);
                           Havoc_Discr_Cond : constant W_Expr_Id :=
                             New_Conditional
                               (Domain      => EW_Prog,
                                Condition   => New_Not
                                  (Domain   => EW_Prog,
                                   Right    => +E.Constr.Id),
                                Then_Part   => +Havoc_Discr);
                        begin
                           T := +Sequence (+Havoc_Discr_Cond, +T);
                        end;
                     end if;
                  end if;

               when Pointer =>
                  T := Pointer_From_Split_Form (E, Params.Ref_Allowed);

                  --  Havoc the references of Ent for volatiles with
                  --  Async_Writers.

                  if Has_Async_Writers (Direct_Mapping_Id (Ent))
                    and then Domain = EW_Prog
                  then
                     pragma Assert (Is_Mutable_In_Why (Ent));
                     pragma Assert (Params.Ref_Allowed);

                     --  Assume dynamic invariant of the object after havoc

                     declare
                        E_Typ    : constant Entity_Id :=
                          Etype (E.Value.Ada_Node);
                        Dyn_Prop : constant W_Pred_Id :=
                          Compute_Dynamic_Invariant (Expr   => +T,
                                                     Ty     => E_Typ,
                                                     Params => Params);
                     begin
                        if Dyn_Prop /= True_Pred then
                           T := +Sequence
                             (New_Assume_Statement (Pred => Dyn_Prop),
                              +T);
                        end if;
                     end;

                     --  Havoc the reference for value

                     pragma Assert (E.Value.Mutable);

                     T := +Sequence
                       (New_Havoc_Call (E.Value.B_Name),
                        +T);

                     --  If the object is mutable then also havoc the address
                     --  and is_null.

                     if E.Mutable then
                        T := +Sequence
                          (New_Havoc_Call (E.Address), +T);
                        T := +Sequence
                          (New_Havoc_Call (E.Is_Null), +T);
                     end if;

                     --  Do not havoc the reference for is_moved, as we don't
                     --  consider that an asynchronous writer could move the
                     --  object.
                  end if;

            end case;

            --  ??? no use of T below when test succeeds? (except for its type)

            if Selector /= Why.Inter.Standard then
               T := +To_Why_Id (Ent, Domain,
                                Selector => Selector,
                                Typ      => Get_Type (T));
            end if;
         end;

      --  Discriminals are not translated in Why3. Use their discriminal link
      --  instead.

      elsif Is_Discriminal (Ent) then
         T := Transform_Identifier (Params   => Params,
                                    Expr     => Expr,
                                    Ent      => Discriminal_Link (Ent),
                                    Domain   => Domain,
                                    Selector => Selector);
      elsif Ekind (Ent) = E_Enumeration_Literal then
         T := Transform_Enum_Literal (Expr, Ent, Domain);

      elsif Sloc (Ent) = Standard_ASCII_Location then
         T :=
           New_Integer_Constant
             (Value => Char_Literal_Value (Constant_Value (Ent)));

      elsif Is_Protected_Component_Or_Discr_Or_Part_Of (Ent) then
         declare
            Prot : constant Entity_Id := Enclosing_Concurrent_Type (Ent);

            pragma Assert (Ekind (Prot) = E_Protected_Type);

            --  The Ada_Node is important here, because that's how we detect
            --  occurrences of "self" in a term later.

            Id : constant W_Identifier_Id :=
              New_Identifier
                (Name     => "self__",
                 Ada_Node => Prot,
                 Typ      => Type_Of_Node (Prot));
         begin
            T := New_Ada_Record_Access
              (Ada_Node => Expr,
               Domain   => Domain,
               Name     =>
                 (if Self_Is_Mutable
                  then New_Deref (Right => Id, Typ => Type_Of_Node (Prot))
                  else +Id),
               Field    => Ent,
               Ty       => Prot);
         end;
      else
         Ada.Text_IO.Put_Line ("[Transform_Identifier] unregistered entity "
                               & Full_Name (Ent));
         raise Program_Error;
      end if;

      --  If we have an object with Async_Writers, we must havoc it before
      --  dereferencing it. Given a ref term t, this produces the sequence:
      --     (__havoc(t); !t)
      --  It is sound (and necessary) to only do that in the program domain. We
      --  can be sure that the relevant Ada code will pass this point at least
      --  once in program domain.

      if Has_Async_Writers (Direct_Mapping_Id (Ent))
        and then Domain = EW_Prog
        and then Need_Deref
        and then Params.Ref_Allowed
      then
         pragma Assert (Is_Mutable_In_Why (Ent));
         declare
            Deref    : constant W_Expr_Id :=
              New_Deref (Ada_Node => Get_Ada_Node (+T),
                         Right    => +T,
                         Typ      => Get_Type (T));
            Dyn_Prop : constant W_Pred_Id :=
              Compute_Dynamic_Invariant (Expr   => +Deref,
                                         Ty     => Etype (Ent),
                                         Params => Params);
            Havoc    : W_Prog_Id := New_Havoc_Call (+T);
         begin
            if Dyn_Prop /= True_Pred then

               --  Assume dynamic invariant of the object after the havoc

               Havoc := +Sequence
                 (Havoc, New_Assume_Statement (Pred => Dyn_Prop));
            end if;

            T := +Sequence (Ada_Node => Get_Ada_Node (+T),
                            Left     => Havoc,
                            Right    => +Deref);
         end;

      elsif Params.Ref_Allowed and then Need_Deref then
         pragma Assert (Is_Mutable_In_Why (Ent));
         T := New_Deref (Ada_Node => Get_Ada_Node (+T),
                         Right    => +T,
                         Typ      => Get_Type (T));
      end if;

      --  If the init_id field is present, use a wrapper type in split form so
      --  that initialization checks are inserted when necessary.

      if Init_Id.Present then
         T := New_Label
           (Ada_Node => Ent,
            Domain   => Domain,
            Labels   => Symbol_Sets.Empty_Set,
            Def      => T,
            Typ      => EW_Split (Etype (Ent), Relaxed_Init => True));
      end if;

      return T;
   end Transform_Identifier;

   -------------------------------------
   -- Transform_Membership_Expression --
   -------------------------------------

   function Transform_Membership_Expression
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id) return W_Expr_Id
   is

      function Initialization_Check_Needed return Boolean;
      --  As the expression of the membership test is evaluated, its top
      --  level initialization flag is always checked. If the expression
      --  is composite, we may also need to check that components are
      --  initialized if the tests involve an equality.

      function Transform_Alternative
        (Var       : W_Expr_Id;
         Alt       : Node_Id;
         Base_Type : W_Type_Id)
         return W_Expr_Id;
      --  If the alternative Alt is a subtype mark, transform it as a simple
      --  membership test "Var in Alt". Otherwise transform it as an equality
      --  test "Var = Alt".

      function Transform_Simple_Membership_Expression
        (Var     : W_Expr_Id;
         In_Expr : Node_Id) return W_Expr_Id;

      ---------------------------------
      -- Initialization_Check_Needed --
      ---------------------------------

      function Initialization_Check_Needed return Boolean is
      begin
         if Present (Alternatives (Expr)) then
            declare
               Alt : Node_Id := First (Alternatives (Expr));
            begin
               Alt := First (Alternatives (Expr));
               while Present (Alt) loop
                  if not (Is_Entity_Name (Alt) and then Is_Type (Entity (Alt)))
                    and then Nkind (Alt) /= N_Range
                  then
                     return True;
                  end if;
                  Next (Alt);
               end loop;
            end;
         end if;
         return False;
      end Initialization_Check_Needed;

      ---------------------------
      -- Transform_Alternative --
      ---------------------------

      function Transform_Alternative
        (Var       : W_Expr_Id;
         Alt       : Node_Id;
         Base_Type : W_Type_Id)
         return W_Expr_Id
      is
         Result    : W_Expr_Id;
         Subdomain : constant EW_Domain :=
           (if Domain = EW_Pred then EW_Term else Domain);
         --  We check equality on initialized objects

      begin
         if (Is_Entity_Name (Alt) and then Is_Type (Entity (Alt)))
           or else Nkind (Alt) = N_Range
         then
            Result :=
              Transform_Simple_Membership_Expression (Var, Alt);
         else
            Result := New_Ada_Equality
              (Typ    => Etype (Left_Opnd (Expr)),
               Left   => Var,
               Right  => Transform_Expr (Expr          => Alt,
                                         Expected_Type => Base_Type,
                                         Domain        => Subdomain,
                                         Params        => Params),
               Domain => Domain);
         end if;

         return Result;
      end Transform_Alternative;

      --------------------------------------------
      -- Transform_Simple_Membership_Expression --
      --------------------------------------------

      function Transform_Simple_Membership_Expression
        (Var     : W_Expr_Id;
         In_Expr : Node_Id) return W_Expr_Id
      is
         True_Expr : constant W_Expr_Id :=
           (if Domain = EW_Pred then +True_Pred else +True_Term);
         Result    : W_Expr_Id;
         Var_Tmp   : constant W_Expr_Id := New_Temp_For_Expr (Var);

      begin
         --  First handle the simpler case of s subtype mark Classwide types
         --  appear as a N_Attribute_Reference.

         if (Nkind (In_Expr) in N_Identifier | N_Expanded_Name
             and then Is_Type (Entity (In_Expr)))
           or else (Nkind (In_Expr) = N_Attribute_Reference
                    and then Get_Attribute_Id (Attribute_Name (In_Expr)) =
                      Attribute_Class)
         then
            declare
               Ty : constant Entity_Id := Unique_Entity (Entity (In_Expr));

            begin
               --  Record subtypes are special

               if Is_Record_Type_In_Why (Ty) then

                  --  We must check for two cases. Ty may be constrained, in
                  --  which case we need to check its dicriminant, or it may
                  --  be tagged, in which case we need to check its tag.

                  declare
                     Discr_Cond : W_Expr_Id := True_Expr;
                     Tag_Cond   : W_Expr_Id := True_Expr;
                     Spec_Ty    : constant Entity_Id :=
                       (if Is_Class_Wide_Type (Ty)
                        then Retysp (Get_Specific_Type_From_Classwide (Ty))
                        else Retysp (Ty));
                     Conc_Var   : constant W_Expr_Id :=
                       Insert_Simple_Conversion
                         (Domain         => Domain,
                          Expr           => Var_Tmp,
                          To             => EW_Abstract (Ty),
                          Force_No_Slide => True);
                     --  If Var is partially initialized, we need to go to the
                     --  concrete type to introduce the checks. Do not check
                     --  for initialization here.
                  begin

                     --  If Ty is constrained, we need to check its
                     --  discriminant.
                     --  It is also the case if Ty's specific type is
                     --  constrained, see RM 3.9 (14).

                     if Root_Retysp (Spec_Ty) /= Spec_Ty
                       and then Count_Discriminants (Spec_Ty) > 0
                       and then Is_Constrained (Spec_Ty)
                     then
                        Discr_Cond := New_Call
                          (Domain => Domain,
                           Name => E_Symb
                             (Root_Retysp (Spec_Ty), WNE_Range_Pred),
                           Args =>
                             Prepare_Args_For_Subtype_Check
                               (Spec_Ty, Conc_Var),
                           Typ  => EW_Bool_Type);
                     end if;

                     --  If Ty is tagged, we need to check its tag

                     if Is_Tagged_Type (Ty)
                       and then Is_Class_Wide_Type (Ty)
                     then

                        --  If we are checking against a classwide type, it is
                        --  enough to check wether Var can be converted to Ty.

                        declare
                           Var_Type : constant Entity_Id :=
                             Get_Ada_Node (+Get_Type (Var_Tmp));
                        begin
                           pragma Assert (Present (Var_Type));

                           if not SPARK_Util.Types.Is_Ancestor (Ty, Var_Type)
                           then
                              Tag_Cond := New_Call
                                (Domain => Domain,
                                 Name => M_Compat_Tags.Compat_Tags_Id,
                                 Args => (1 => New_Tag_Access
                                          (Domain   => EW_Term,
                                           Name     => Var_Tmp,
                                           Ty       => Var_Type),
                                          2 => +E_Symb (E => Ty,
                                                        S => WNE_Tag)),
                                 Typ  => EW_Bool_Type);
                           end if;
                        end;
                     elsif Is_Tagged_Type (Ty) then

                        --  If we are checking against a specific type, then
                        --  the tags of Var and Ty must match.

                        Tag_Cond := New_Call
                          (Domain => Domain,
                           Name => Why_Eq,
                           Args => (1 => New_Tag_Access
                                    (Domain   => EW_Term,
                                     Name     => Var_Tmp,
                                     Ty       =>
                                       Get_Ada_Node (+Get_Type (Var_Tmp))),
                                    2 => +E_Symb (E => Ty,
                                                  S => WNE_Tag)),
                           Typ  => EW_Bool_Type);
                     end if;

                     --  Go back to the appropriate domain

                     declare
                        Condition : constant W_Expr_Id :=
                          New_And_Expr (Discr_Cond, Tag_Cond, Domain);
                     begin
                        if Domain = EW_Pred then
                           Result := Condition;
                        else
                           Result :=
                             New_Conditional
                               (Domain    => Domain,
                                Condition => Condition,
                                Then_Part => True_Expr,
                                Else_Part =>
                                  New_Literal (Domain => EW_Term,
                                               Value => EW_False),
                                Typ       => EW_Bool_Type);
                        end if;
                     end;
                  end;

               elsif Is_Array_Type (Ty) then

                  --  There are no constraints to check if the type is
                  --  unconstrained.

                  if Is_Constrained (Ty) then
                     declare
                        Var_Type   : constant Entity_Id :=
                          Get_Ada_Node (+Get_Type (Var_Tmp));
                        False_Expr : constant W_Expr_Id :=
                          (if Domain = EW_Pred then +False_Pred
                           else +False_Term);

                     begin
                        --  For static arrays, we do the check statically

                        if Is_Static_Array_Type (Ty)
                          and then Is_Static_Array_Type (Var_Type)
                        then
                           declare
                              Ty_Index  : Node_Id := First_Index (Ty);
                              Var_Index : Node_Id := First_Index (Var_Type);
                           begin
                              if Ekind (Var_Type) = E_String_Literal_Subtype
                              then
                                 if Expr_Value
                                     (String_Literal_Low_Bound (Var_Type))
                                   /= Expr_Value
                                       (Low_Bound (Get_Range (Ty_Index)))
                                   or else Static_Array_Length (Var_Type, 1)
                                   /= Static_Array_Length (Ty, 1)
                                 then
                                    Result := False_Expr;
                                 else
                                    Result := True_Expr;
                                 end if;
                              else
                                 Result := True_Expr;

                                 while Present (Ty_Index) loop
                                    if Expr_Value
                                        (High_Bound (Get_Range (Ty_Index)))
                                      /= Expr_Value
                                        (High_Bound (Get_Range (Var_Index)))
                                      or else
                                        Expr_Value
                                          (Low_Bound (Get_Range (Ty_Index)))
                                      /= Expr_Value
                                        (Low_Bound (Get_Range (Var_Index)))
                                    then
                                       Result := False_Expr;
                                       exit;
                                    end if;
                                    Ty_Index := Next_Index (Ty_Index);
                                    Var_Index := Next_Index (Var_Index);
                                 end loop;
                              end if;
                           end;

                        --  Otherwise, we translate the check as the
                        --  conjunction of the equality between each pair of
                        --  bounds.

                        else
                           Result := +New_Bounds_Equality
                             (Var_Tmp, Ty, Domain);
                        end if;
                     end;
                  else
                     Result := True_Expr;
                  end if;

               --  For a constrained access type whose root is not constrained,
               --  use the range predicate.

               elsif Is_Access_Type (Ty) then
                  if not Is_Constrained (Root_Retysp (Ty))
                    and then Is_Constrained (Ty)
                  then
                     Result := New_Call
                       (Domain => Domain,
                        Name   => E_Symb (Ty, WNE_Range_Pred),
                        Args   =>
                          Prepare_Args_For_Access_Subtype_Check (Ty, Var_Tmp),
                        Typ    => EW_Bool_Type);
                  else
                     Result := True_Expr;
                  end if;

                  --  For non null access types, check null exclusion

                  if Can_Never_Be_Null (Ty) then
                     Result := New_And_Then_Expr
                       (Left   => Result,
                        Right  => New_Not
                          (Right  => New_Pointer_Is_Null_Access
                               (E    => Ty,
                                Name => Var_Tmp),
                           Domain => Domain),
                        Domain => Domain);
                  end if;

               else
                  pragma Assert (Is_Scalar_Type (Ty));
                  if Type_Is_Modeled_As_Base (Ty) then
                     Result := New_Dynamic_Property (Domain => Domain,
                                                     Ty     => Ty,
                                                     Expr   => Var_Tmp);
                  else
                     declare
                        Name : constant W_Identifier_Id :=
                          (if Is_Standard_Boolean_Type (Ty) then
                                M_Boolean.Range_Pred
                           else E_Symb (Ty, WNE_Range_Pred));
                     begin
                        Result :=
                          New_Call (Domain => Domain,
                                    Name => Name,
                                    Args => (1 => Var_Tmp),
                                    Typ  => EW_Bool_Type);
                     end;
                  end if;
               end if;

               --  Possibly include a predicate in the type membership test

               if Has_Predicates (Ty) then
                  declare
                     Init_Var : constant W_Expr_Id := New_Temp_For_Expr
                       (E =>
                          (if Is_Init_Wrapper_Type (Get_Type (Var))
                           then Insert_Checked_Conversion
                             (Ada_Node => Left_Opnd (Expr),
                              Domain   => Domain,
                              Expr     => Var_Tmp,
                              To       => EW_Abstract (Ty))
                           else Var_Tmp));
                  begin
                     Result := New_And_Expr
                       (Result,
                        Boolean_Expr_Of_Pred
                          (Compute_Dynamic_Predicate
                               (+Init_Var, Ty, Params),
                           Domain),
                        Domain);
                     Result := Binding_For_Temp (Domain  => Domain,
                                                 Tmp     => Init_Var,
                                                 Context => Result);
                  end;
               end if;
            end;
         else
            Result := Range_Expr (In_Expr, Var_Tmp, Domain, Params);
         end if;

         Result := Binding_For_Temp (Domain  => Domain,
                                     Tmp     => Var_Tmp,
                                     Context => Result);

         return Binding_For_Temp
           (Domain  => Domain,
            Tmp     => Var_Tmp,
            Context => Result);
      end Transform_Simple_Membership_Expression;

      Var          : constant Node_Id := Left_Opnd (Expr);
      Result       : W_Expr_Id;
      Relaxed_Init : constant Boolean :=
        not Initialization_Check_Needed
        and then Expr_Has_Relaxed_Init (Var, No_Eval => False);
      Base_Type    : W_Type_Id :=
        (if Is_Record_Type_In_Why (Etype (Var))
         then EW_Abstract
           (Root_Retysp (Etype (Var)),
            Relaxed_Init => Relaxed_Init)
      --  For records, checks are done on the root type

         elsif Relaxed_Init then Type_Of_Node (Var)
      --  Do not check initialization on composite types

         else Base_Why_Type (Var));

      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Var_Expr  : W_Expr_Id;

   --  Start of processing for Transform_Membership_Expression

   begin
      --  For ranges and membership, "bool" should be mapped to "int"

      if Base_Type = EW_Bool_Type then
         Base_Type := EW_Int_Type;
      end if;
      Var_Expr := Transform_Expr (Var, Base_Type, Subdomain, Params);

      if Initialization_Check_Needed then
         Var_Expr := Insert_Initialization_Check
           (Ada_Node               => Var,
            E                      => Etype (Var),
            Name                   => Var_Expr,
            Domain                 => Subdomain,
            Exclude_Always_Relaxed => False);
      end if;

      if Present (Alternatives (Expr)) then
         declare
            Alt : Node_Id;
         begin
            Var_Expr := New_Temp_For_Expr (Var_Expr, True);
            Alt := Last (Alternatives (Expr));
            Result := Transform_Alternative (Var_Expr, Alt, Base_Type);

            Prev (Alt);
            while Present (Alt) loop
               Result := New_Or_Else_Expr
                 (Left   => Transform_Alternative (Var_Expr, Alt, Base_Type),
                  Right  => Result,
                  Domain => Domain);
               Prev (Alt);
            end loop;
            Result := Binding_For_Temp (Domain  => Domain,
                                        Tmp     => Var_Expr,
                                        Context => Result);
         end;
      else
         Result :=
           Transform_Simple_Membership_Expression
             (Var_Expr, Right_Opnd (Expr));
      end if;

      --  Inverse the result if the operator is NOT IN

      if Nkind (Expr) = N_Not_In then
         if Domain = EW_Term then
            Result := New_Call
              (Ada_Node => Expr,
               Domain   => Domain,
               Name     => M_Boolean.Notb,
               Args     => (1 => Result),
               Typ      => EW_Bool_Type);

         else
            Result := New_Not (Right => Result, Domain => Domain);
         end if;
      end if;

      return Result;
   end Transform_Membership_Expression;

   --------------------------------------------
   -- Transform_Non_Binary_Modular_Operation --
   --------------------------------------------

   function Transform_Non_Binary_Modular_Operation
     (Ada_Node   : Node_Id;
      Ada_Type   : Entity_Id;
      Domain     : EW_Domain;
      Op         : N_Op;
      Left_Opnd  : W_Expr_Id := Why_Empty;
      Right_Opnd : W_Expr_Id;
      Rep_Type   : W_Type_Id;
      Modulus    : Uint) return W_Expr_Id
   is
      T : W_Expr_Id;

   begin
      --  GNAT only supports non-binary modulus up to 2**32. We use this
      --  limitation here to simplify the implementation, so we check this
      --  is the case here.

      if Modulus >= UI_Expon (2, 32) then
         raise Program_Error;
      end if;

      case Op is

         --  Transform (-Y) into:
         --    (Modulus - Y) modulo Modulus
         --  We add the extra modulo in order to deal with the special case
         --  of -0. We use modulo instead of a test in order to have a fully
         --  computational interpretation.

         when N_Op_Minus =>
            pragma Assert (Left_Opnd = Why_Empty);

            declare
               Modulus_Expr : constant W_Expr_Id :=
                 New_Modular_Constant
                   (Value => Modulus,
                    Typ   => Rep_Type);

               Sub : constant W_Expr_Id :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => MF_BVs (Rep_Type).Sub,
                    Args     =>
                      (1 => Modulus_Expr,
                       2 => Right_Opnd),
                    Typ      => Rep_Type);

            begin
               T := New_Call (Domain => Domain,
                              Name   => MF_BVs (Rep_Type).Urem,
                              Args   =>
                                (1 => Sub,
                                 2 => Modulus_Expr),
                              Typ    => Rep_Type);
            end;

         --  Transform (X + Y) into:
         --    if Modulus - X <= Y
         --    then (X + Y) - Modulus
         --    else X + Y

         when N_Op_Add =>
            declare
               BV            : constant M_BV_Type := MF_BVs (Rep_Type);
               Modulus_Expr  : constant W_Expr_Id :=
                 New_Modular_Constant (Value => Modulus,
                                       Typ   => Rep_Type);
               Add_Expr      : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Add,
                           Args     => (1 => Left_Opnd,
                                        2 => Right_Opnd),
                           Typ   => Rep_Type);
               Add_Id        : constant W_Expr_Id :=
                 New_Temp_For_Expr (E => Add_Expr);
               Overflow_Test : constant W_Expr_Id :=
                 New_Call (Domain => Domain,
                           Name   => BV.Ule,
                           Args   =>
                             (1 => New_Call (Domain => Domain,
                                             Name   => BV.Sub,
                                             Args   => (1 => Modulus_Expr,
                                                        2 => Left_Opnd),
                                             Typ    => Rep_Type),
                              2 => Right_Opnd),
                           Typ    => EW_Bool_Type);
               Modulo_Expr   : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Sub,
                           Args     => (1 => Add_Id,
                                        2 => Modulus_Expr),
                           Typ      => Rep_Type);
               Ite_Expr      : constant W_Conditional_Id :=
                 New_Conditional (Ada_Node    => Ada_Node,
                                  Domain      => Domain,
                                  Condition   => Overflow_Test,
                                  Then_Part   => Modulo_Expr,
                                  Else_Part   => Add_Id,
                                  Typ         => Rep_Type);
            begin
               T := Binding_For_Temp (Ada_Node => Ada_Node,
                                      Domain   => Domain,
                                      Tmp      => Add_Id,
                                      Context  => +Ite_Expr);
            end;

         --  Transform (X - Y) into:
         --    if Y > X
         --    then (X - Y) + Modulus
         --    else X - Y

         when N_Op_Subtract =>
            declare
               BV            : constant M_BV_Type := MF_BVs (Rep_Type);
               Modulus_Expr  : constant W_Expr_Id :=
                 New_Modular_Constant (Value => Modulus,
                                       Typ   => Rep_Type);
               Sub_Expr      : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Sub,
                           Args     => (1 => Left_Opnd,
                                        2 => Right_Opnd),
                           Typ   => Rep_Type);
               Sub_Id        : constant W_Expr_Id :=
                 New_Temp_For_Expr (E => Sub_Expr);
               Overflow_Test : constant W_Expr_Id :=
                 New_Call (Domain   => Domain,
                           Name     => BV.Ult,
                           Args     => (1 => Left_Opnd,
                                        2 => Right_Opnd),
                           Typ      => EW_Bool_Type);
               Modulo_Expr   : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Add,
                           Args     => (1 => Sub_Id,
                                        2 => Modulus_Expr),
                           Typ      => Rep_Type);
               Ite_Expr      : constant W_Conditional_Id :=
                 New_Conditional (Ada_Node    => Ada_Node,
                                  Domain      => Domain,
                                  Condition   => Overflow_Test,
                                  Then_Part   => Modulo_Expr,
                                  Else_Part   => Sub_Id,
                                  Typ         => Rep_Type);
            begin
               T := Binding_For_Temp (Ada_Node => Ada_Node,
                                      Domain   => Domain,
                                      Tmp      => Sub_Id,
                                      Context  => +Ite_Expr);
            end;

         --  In those cases where the multiplication may not fit in the size of
         --  bitvector of [Rep_Type], convert both operands to the next size of
         --  bitvector, do the multiplication without overflow in that larger
         --  type, then apply the modulus and convert back to the original
         --  type.

         when N_Op_Multiply =>
            declare
               Next_Bv      : constant W_Type_Id :=
                 (if Modulus < UI_Expon (2, 8) then
                    (if Modular_Size (Ada_Type) < 16 then EW_BitVector_16_Type
                     else Rep_Type)
                  elsif Modulus < UI_Expon (2, 16) then
                     (if Modular_Size (Ada_Type) < 32 then EW_BitVector_32_Type
                     else Rep_Type)
                  else
                     EW_BitVector_64_Type);
               Modulus_Expr : constant W_Expr_Id :=
                 New_Modular_Constant (Value => Modulus,
                                       Typ   => Next_Bv);
               Next_Left    : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Domain => Domain,
                                           Expr   => Left_Opnd,
                                           To     => Next_Bv);
               Next_Right   : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Domain => Domain,
                                           Expr   => Right_Opnd,
                                           To     => Next_Bv);
               Mul_Expr     : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => MF_BVs (Next_Bv).Mult,
                           Args     => (1 => Next_Left,
                                        2 => Next_Right),
                           Typ      => Next_Bv);
               Modulo_Expr  : constant W_Expr_Id :=
                 New_Call (Name   => MF_BVs (Next_Bv).Urem,
                           Domain => Domain,
                           Args   => (1 => Mul_Expr,
                                      2 => Modulus_Expr),
                           Typ    => Next_Bv);
            begin
               T := Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                              Domain   => Domain,
                                              Expr     => Modulo_Expr,
                                              To       => Rep_Type);
            end;

         --  Translate exponentiation on mathematical integers to avoid
         --  the wrap-around semantics on bitvector types. Indeed, it is not
         --  possible to go to a bigger bitvector type here as there are no
         --  such bitvector type even for 8 bit bitvectors.

         when N_Op_Expon =>
            declare
               Modulus_Expr : constant W_Expr_Id :=
                 New_Integer_Constant (Value => Modulus);
               Int_Left     : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Domain => Domain,
                                           Expr   => Left_Opnd,
                                           To     => EW_Int_Type);
               Exp_Expr     : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => M_Int_Power.Power,
                           Args     => (1 => Int_Left,
                                        2 => Right_Opnd),
                           Typ      => EW_Int_Type);
               Modulo_Expr  : constant W_Expr_Id :=
                 New_Call (Name   => M_Int_Div.Rem_Id,
                           Domain => Domain,
                           Args   => (1 => Exp_Expr,
                                      2 => Modulus_Expr),
                           Typ    => EW_Int_Type);
            begin
               T := Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                              Domain   => Domain,
                                              Expr     => Modulo_Expr,
                                              To       => Rep_Type);
            end;

         when others =>
            raise Program_Error;
      end case;

      return T;
   end Transform_Non_Binary_Modular_Operation;

   ---------------------------
   -- Transform_Pledge_Call --
   ---------------------------

   function Transform_Pledge_Call
     (Brower : Entity_Id;
      Def    : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
      Pledge_Params    : constant Transformation_Params :=
        (File        => Params.File,
         Phase       => Params.Phase,
         Gen_Marker  => Params.Gen_Marker,
         Ref_Allowed => Params.Ref_Allowed,
         Old_Policy  => Use_Map);
      --  Inside pledges, Old can be used to refer to values at time of borrow

      Brower_Id        : constant W_Identifier_Id :=
        New_Temp_Identifier
          (Base_Name => "brower",
           Typ       => Type_Of_Node (Etype (Brower)));
      Borrowed         : constant Entity_Id :=
        Get_Borrowed_Entity (Brower);
      Borrowed_Id      : constant W_Identifier_Id :=
        New_Temp_Identifier
          (Base_Name => "borrowed",
           Typ       => Type_Of_Node (Etype (Borrowed)));
      Path_Constraints : constant W_Pred_Id :=
        Compute_Assumption_For_Borrow
          (Brower      => Brower,
           Borrowed_Id => Borrowed_Id,
           Params      => Params);
      --  Predicate expressing that it is possible to access the borrowed
      --  expression in borrowed_id.

      Brower_E       : constant W_Expr_Id :=
        (if Ekind (Brower) = E_Function
         then
           (if Result_Is_Mutable
            then New_Deref (Right => Result_Name,
                            Typ   => Get_Typ (Result_Name))
            else +Result_Name)
         else Transform_Identifier
           (Params   => Params,
            Expr     => Brower,
            Ent      => Brower,
            Domain   => EW_Term));
      --  The expression for the borrower. If we are translating the pledge of
      --  a traversal function, it is the result of the call. Otherwise, it is
      --  the borrower entity.
      Brower_Is_Null : constant W_Expr_Id := New_Pointer_Is_Null_Access
        (E    => Retysp (Etype (Brower)),
         Name => Brower_E);
      --  Get the is_null field of Brower. We store it before we override
      --  Brower in the symbol table.

      Save_Result_Name    : constant W_Identifier_Id := Result_Name;
      Save_Res_Is_Mutable : constant Boolean := Result_Is_Mutable;
      Save_Map_For_Old    : constant Ada_To_Why_Ident.Map := Map_For_Old;

   begin
      --  For a borrow Brower := Borrowed.Path, we want to generate:
      --
      --  forall Brower_id, borrowed_id [pledge borrowed_id Brower_id].
      --    (* The borrower respects its dynamic invariant *)
      --    dyn_inv brower_id ->
      --    (* Brower and borrowed are linked by the pledge *)
      --    pledge borrowed_id brower_id ->
      --    (* Constraints in borrowed on the path leading to brower are
      --       preserved *)
      --    same_constraints_on_path <borrowed, borrowed_id> ->
      --    (* The Is_Null component of the Brower cannot be assigned.
      --       ??? We could also preserve the address. *)
      --    brower_id.is_null = brower.is_null ->
      --       def
      --
      --  Note that we do not assume the dynamic property of borrowed as the
      --  pledge should be usable to reassess the dynamic invariant of the
      --  borrowed object. It should not cause issues as the pledge should
      --  only mention borrowed.path and not borrowed.

      --  Insert Brower_Id and Borrowed_Id in the symbol table. If we are
      --  translating a pledge of a traversal function, the borrower is the
      --  result of the call.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      if Ekind (Brower) = E_Function then
         Result_Name := Brower_Id;
         Result_Is_Mutable := False;
      else
         Insert_Entity (Brower, Brower_Id);
      end if;
      Insert_Entity (Borrowed, Borrowed_Id);

      --  If we are forcing the use of the map for old, we need to reset it.
      --  It will be reset at the end of the translation to avoid poluting
      --  other potential users.
      --  ??? Should we use a stack for the map of Old, or possibly have a
      --  temporary map?

      if Params.Old_Policy /= Use_Map then
         Reset_Map_For_Old;
      end if;

      --  Transform the pledge in the pred domain, we will lift it to other
      --  domains afterward.

      declare
         Res           : W_Expr_Id := Transform_Expr
           (Expr   => Def,
            Domain => EW_Pred,
            Params => Pledge_Params);
         Pledge_Call   : constant W_Expr_Id :=
           New_Pledge_Call
             (E            => Brower,
              Borrowed_Arg => +Borrowed_Id,
              Brower_Arg   => +Brower_Id,
              Ref_Allowed  =>
                Params.Phase in Generate_VCs | Generate_For_Body);
         Assumption    : constant W_Expr_Id := New_And_Expr
           (Conjuncts => (1 => +Pred_Of_Boolean_Term (+Pledge_Call),
                          2 => +Compute_Dynamic_Invariant
                            (Expr        => +Brower_Id,
                             Ty          => Etype (Brower),
                             Params      => Params,
                             Initialized => True_Term),
                          3 => +Path_Constraints,
                          4 => New_Comparison
                            (Symbol => Why_Eq,
                             Left   => Brower_Is_Null,
                             Right  => New_Pointer_Is_Null_Access
                               (E    => Retysp (Etype (Brower)),
                                Name => +Brower_Id),
                             Domain => EW_Pred)),
            Domain    => EW_Pred);
      begin
         Res := New_Conditional
                 (Condition => Assumption,
                  Domain    => EW_Pred,
                  Then_Part => Res,
                  Typ       => EW_Bool_Type);

         Res :=
           +New_Universal_Quantif
           (Binders  =>
              Binder_Type'(B_Name => Borrowed_Id, others => <>)
            & Binder_Type'(B_Name => Brower_Id, others => <>),
            Triggers => New_Triggers
              (Triggers =>
                   (1 => New_Trigger (Terms => (1 => Pledge_Call)))),
            Pred     => +Res);

         --  For the term domains, just lift it directly

         if Domain in EW_Terms then
            Res := Boolean_Expr_Of_Pred (+Res, Domain);

         --  In the prog domain, we want to insert checks. We generate:
         --  ignore (let brower_id = any Brower_ty in
         --          let borrowed_id = any borrowed_ty in
         --          assume {assumption};
         --          def);
         --          any bool ensures { result = Res }
         --  where Res is the translation of the pledge in the Pred domain.
         --  Note that the mechanism is similar to the one used for translating
         --  quantified expressions.

         elsif Domain = EW_Prog then
            declare
               Checks : W_Prog_Id :=
                 Sequence
                   (Left  => New_Assume_Statement
                      (Pred => +Assumption),
                    Right => +Transform_Expr (Expr    => Def,
                                              Domain  => EW_Prog,
                                              Params  => Pledge_Params));
            begin
               Checks := New_Binding
                 (Name    => Brower_Id,
                  Def     => New_Any_Expr
                    (Return_Type => Get_Typ (Brower_Id),
                     Labels      => Symbol_Sets.Empty_Set),
                  Context => New_Binding
                    (Domain  => EW_Prog,
                     Name    => Borrowed_Id,
                     Def     => New_Any_Expr
                       (Return_Type => Get_Typ (Borrowed_Id),
                        Labels      => Symbol_Sets.Empty_Set),
                     Context => +Checks,
                     Typ     => EW_Bool_Type),
                  Typ     => EW_Bool_Type);
               Res := +Sequence
                 (Left  => New_Ignore (Prog => Checks),
                  Right => New_Any_Expr
                    (Post        => +New_Comparison
                         (Symbol => Why_Eq,
                          Left   => +New_Result_Ident (EW_Bool_Type),
                          Right  => +Res,
                          Domain => EW_Pred),
                     Return_Type => EW_Bool_Type,
                     Labels      => Symbol_Sets.Empty_Set));
            end;
         end if;

         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         Result_Name := Save_Result_Name;
         Result_Is_Mutable := Save_Res_Is_Mutable;

         --  If the map for old is not used in the calling context, introduce
         --  mappings for old variables in the pledge expression and reset the
         --  map for old to its former value.

         if Params.Old_Policy /= Use_Map then
            for C in Map_For_Old.Iterate loop
               declare
                  N     : constant Node_Id := Ada_To_Why_Ident.Key (C);
                  Name  : constant W_Identifier_Id :=
                    Ada_To_Why_Ident.Element (C);
               begin
                  Res := New_Typed_Binding
                    (Domain  => Domain,
                     Name    => Name,
                     Def     => +Insert_Checked_Conversion
                       (Ada_Node => N,
                        Domain   => Domain,
                        Expr     =>
                          Transform_Attribute_Old (N, Domain, Params),
                        To       => Get_Typ (Name)),
                     Context => Res);
               end;
            end loop;

            Old_Map := Save_Map_For_Old;
         end if;

         return Res;
      end;
   end Transform_Pledge_Call;

   ----------------------
   -- Transform_Pragma --
   ----------------------

   function Transform_Pragma
     (Prag  : Node_Id;
      Force : Boolean) return W_Prog_Id
   is
      Prag_Id : constant Pragma_Id := Get_Pragma_Id (Prag);

      procedure tip;
      --  A dummy procedure called when pragma Inspection_Point is processed.
      --  This is just to help debugging Why generation. If a pragma
      --  Inspection_Point is added to a source program, then breaking on
      --  tip will get you to that point in the program.

      ---------
      -- tip --
      ---------

      procedure tip is
      begin
         null;
      end tip;

   --  Start of processing for Transform_Pragma

   begin
      case Prag_Id is

         --  Ignore pragma Check for preconditions and postconditions

         when Pragma_Check =>
            return Transform_Pragma_Check (Prag, Force);

         --  Pragma Overflow_Mode should have an effect on proof, but is
         --  currently ignored (and a corresponding warning is issued
         --  during marking).

         when Pragma_Overflow_Mode =>
            return +Void;

         --  Unless Force is True to force the translation of pragmas
         --  Precondition and Postcondition (for those pragmas declared in
         --  a subprogram body), these pragmas are translated elsewhere.

         when Pragma_Precondition
            | Pragma_Postcondition
         =>
            if Force then
               declare
                  Expr   : constant Node_Id :=
                    Expression (First (Pragma_Argument_Associations (Prag)));
                  Params : Transformation_Params := Assert_Params;
                  Result : W_Prog_Id;

               begin
                  Result := New_Ignore
                    (Prog =>
                       +Transform_Expr (Expr, EW_Prog, Params => Params));
                  Params.Gen_Marker := GM_All;
                  Result := Sequence
                    (Result,
                     New_Located_Assert
                       (Expr,
                        +Transform_Expr (Expr, EW_Pred, Params => Params),
                        VC_Assert,
                        EW_Assert));
                  return Result;
               end;
            else
               return +Void;
            end if;

         when Pragma_Interrupt_Priority
            | Pragma_Priority
         =>
            return Transform_Priority_Pragmas (Prag);

         --  Pragma Inspection_Point is ignored, but we insert a call to a
         --  dummy procedure, to allow to break on it during debugging.

         when Pragma_Inspection_Point =>
            tip;
            return +Void;

         --  Do not issue a warning on invariant pragmas, as one is already
         --  issued on the corresponding type in SPARK.Definition.

         when Pragma_Invariant
            | Pragma_Type_Invariant
            | Pragma_Type_Invariant_Class
         =>
            return +Void;

         --  Remaining pragmas fall into two major groups:
         --
         --  Group 1 - ignored
         --
         --  Pragmas that do not need any proof processing, either because:
         --  . they are defined by SPARK 2014, or
         --  . they are already taken into account elsewhere (contracts)
         --  . they have no effect on verification

         --  Group 1a - RM Table 16.1, Ada language-defined pragmas marked
         --  "Yes".

         when  --  Pragma_Assert is transformed into pragma Check handled above
              Pragma_Assertion_Policy
            | Pragma_Atomic
            | Pragma_Atomic_Components
            | Pragma_Attach_Handler
            | Pragma_Convention
            | Pragma_CPU
            | Pragma_Detect_Blocking
            | Pragma_Elaborate
            | Pragma_Elaborate_All
            | Pragma_Elaborate_Body
            | Pragma_Export
            | Pragma_Import
            | Pragma_Independent
            | Pragma_Independent_Components
            | Pragma_Inline
            --  Pragma_Inspection_Point is handled specially above
            | Pragma_Interrupt_Handler
            --  Pragma_Interrupt_Priority is handled specially above
            | Pragma_Linker_Options
            | Pragma_List
            | Pragma_Locking_Policy
            | Pragma_No_Return
            | Pragma_Normalize_Scalars
            | Pragma_Optimize
            | Pragma_Pack
            | Pragma_Page
            | Pragma_Partition_Elaboration_Policy
            | Pragma_Preelaborable_Initialization
            | Pragma_Preelaborate
            --  Pragma_Priority is handled specially above
            | Pragma_Profile
            | Pragma_Pure
            | Pragma_Queuing_Policy
            | Pragma_Relative_Deadline
            | Pragma_Restrictions
            | Pragma_Reviewable
            | Pragma_Suppress
            | Pragma_Unchecked_Union
            | Pragma_Unsuppress
            | Pragma_Volatile
            | Pragma_Volatile_Components

         --  Group 1b - RM Table 16.2, SPARK language-defined pragmas marked
         --  "Yes", whose effect on proof is taken care of somewhere else.

            | Pragma_Abstract_State
            --  Pragma_Assert_And_Cut and Pragma_Assume are transformed into
            --  pragma Check handled above.
            | Pragma_Async_Readers
            | Pragma_Async_Writers
            | Pragma_Constant_After_Elaboration
            | Pragma_Contract_Cases
            | Pragma_Default_Initial_Condition
            | Pragma_Depends
            | Pragma_Effective_Reads
            | Pragma_Effective_Writes
            | Pragma_Extensions_Visible
            | Pragma_Ghost
            | Pragma_Global
            | Pragma_Initial_Condition
            | Pragma_Initializes
            --  Pragma_Loop_Invariant is transformed into pragma Check handled
            --  above.
            | Pragma_Loop_Variant
            | Pragma_No_Caching
            | Pragma_Part_Of
            | Pragma_Refined_Depends
            | Pragma_Refined_Global
            | Pragma_Refined_Post
            | Pragma_Refined_State
            | Pragma_SPARK_Mode
            | Pragma_Unevaluated_Use_Of_Old
            | Pragma_Volatile_Function

         --  Group 1c - RM Table 16.3, GNAT implementation-defined pragmas
         --  marked "Yes".

            | Pragma_Ada_83
            | Pragma_Ada_95
            | Pragma_Ada_05
            | Pragma_Ada_12
            | Pragma_Ada_2005
            | Pragma_Ada_2012
            | Pragma_Annotate
            | Pragma_Assume_No_Invalid_Values
            --  Pragma_Check is handled specially above
            | Pragma_Check_Policy
            --  Pragma_Compile_Time_Error, Pragma_Compile_Time_Warning and
            --  Pragma_Debug are removed by FE and handled thus below.
            | Pragma_Default_Scalar_Storage_Order
            | Pragma_Export_Function
            | Pragma_Export_Procedure
            | Pragma_Ignore_Pragma
            | Pragma_Inline_Always
            --  Pragma_Invariant is handled specially above
            | Pragma_Linker_Section
            | Pragma_Max_Queue_Length
            | Pragma_No_Elaboration_Code_All
            | Pragma_No_Heap_Finalization
            | Pragma_No_Tagged_Streams
            --  Pragma_Overflow_Mode is handled specially above
            | Pragma_Post
            --  Pragma_Postcondition is handled specially above
            | Pragma_Post_Class
            | Pragma_Pre
            --  Pragma_Precondition is handled specially above
            | Pragma_Pre_Class
            | Pragma_Predicate
            | Pragma_Predicate_Failure
            | Pragma_Provide_Shift_Operators
            | Pragma_Pure_Function
            | Pragma_Restriction_Warnings
            | Pragma_Secondary_Stack_Size
            | Pragma_Style_Checks
            | Pragma_Test_Case
            --  Pragma_Type_Invariant and Pragma_Type_Invariant_Class are
            --  handled specially above.
            | Pragma_Unmodified
            | Pragma_Unreferenced
            | Pragma_Unused
            | Pragma_Validity_Checks
            | Pragma_Volatile_Full_Access
            | Pragma_Warnings
            | Pragma_Weak_External
         =>
            return +Void;

         --  Group 1d - pragma that are re-written and/or removed by the
         --  front-end in GNATprove, so they should never be seen here.
         when Pragma_Assert
            | Pragma_Assert_And_Cut
            | Pragma_Assume
            | Pragma_Compile_Time_Error
            | Pragma_Compile_Time_Warning
            | Pragma_Debug
            | Pragma_Loop_Invariant
         =>
            raise Program_Error;

         --  Group 2 - Remaining pragmas, enumerated here rather than a "when
         --  others" to force re-consideration when SNames.Pragma_Id is
         --  extended.
         --
         --  These can all be ignored - we have already generated a warning
         --  during Marking. In the future, these pragmas may move to be fully
         --  ignored or to be processed with more semantic detail as required.

         --  Group 2a - GNAT Defined and obsolete pragmas
         when Pragma_Abort_Defer
            | Pragma_Allow_Integer_Address
            | Pragma_Attribute_Definition
            | Pragma_C_Pass_By_Copy
            | Pragma_Check_Float_Overflow
            | Pragma_Check_Name
            | Pragma_Comment
            | Pragma_Common_Object
            | Pragma_Compiler_Unit
            | Pragma_Compiler_Unit_Warning
            | Pragma_Complete_Representation
            | Pragma_Complex_Representation
            | Pragma_Component_Alignment
            | Pragma_Controlled
            | Pragma_Convention_Identifier
            | Pragma_CPP_Class
            | Pragma_CPP_Constructor
            | Pragma_CPP_Virtual
            | Pragma_CPP_Vtable
            | Pragma_Debug_Policy
            | Pragma_Default_Storage_Pool
            | Pragma_Disable_Atomic_Synchronization
            | Pragma_Dispatching_Domain
            | Pragma_Elaboration_Checks
            | Pragma_Eliminate
            | Pragma_Enable_Atomic_Synchronization
            | Pragma_Export_Object
            | Pragma_Export_Value
            | Pragma_Export_Valued_Procedure
            | Pragma_Extend_System
            | Pragma_Extensions_Allowed
            | Pragma_External
            | Pragma_External_Name_Casing
            | Pragma_Fast_Math
            | Pragma_Favor_Top_Level
            | Pragma_Finalize_Storage_Only
            | Pragma_Ident
            | Pragma_Implementation_Defined
            | Pragma_Implemented
            | Pragma_Implicit_Packing
            | Pragma_Import_Function
            | Pragma_Import_Object
            | Pragma_Import_Procedure
            | Pragma_Import_Valued_Procedure
            | Pragma_Initialize_Scalars
            | Pragma_Inline_Generic
            | Pragma_Interface
            | Pragma_Interface_Name
            | Pragma_Interrupt_State
            | Pragma_Keep_Names
            | Pragma_License
            | Pragma_Link_With
            | Pragma_Linker_Alias
            | Pragma_Linker_Constructor
            | Pragma_Linker_Destructor
            | Pragma_Loop_Optimize
            | Pragma_Machine_Attribute
            | Pragma_Main
            | Pragma_Main_Storage
            | Pragma_Memory_Size
            | Pragma_No_Body
            | Pragma_No_Inline
            | Pragma_No_Run_Time
            | Pragma_No_Strict_Aliasing
            | Pragma_Obsolescent
            | Pragma_Optimize_Alignment
            | Pragma_Ordered
            | Pragma_Overriding_Renamings
            | Pragma_Passive
            | Pragma_Persistent_BSS
            | Pragma_Polling
            | Pragma_Prefix_Exception_Messages
            | Pragma_Priority_Specific_Dispatching
            | Pragma_Profile_Warnings
            | Pragma_Propagate_Exceptions
            | Pragma_Psect_Object
            | Pragma_Rational
            | Pragma_Ravenscar
            | Pragma_Remote_Access_Type
            | Pragma_Rename_Pragma
            | Pragma_Restricted_Run_Time
            | Pragma_Share_Generic
            | Pragma_Shared
            | Pragma_Short_Circuit_And_Or
            | Pragma_Short_Descriptors
            | Pragma_Simple_Storage_Pool_Type
            | Pragma_Source_File_Name
            | Pragma_Source_File_Name_Project
            | Pragma_Source_Reference
            | Pragma_Static_Elaboration_Desired
            | Pragma_Storage_Unit
            | Pragma_Stream_Convert
            | Pragma_Subtitle
            | Pragma_Suppress_All
            | Pragma_Suppress_Debug_Info
            | Pragma_Suppress_Exception_Locations
            | Pragma_Suppress_Initialization
            | Pragma_System_Name
            | Pragma_Task_Info
            | Pragma_Task_Name
            | Pragma_Task_Storage
            | Pragma_Thread_Local_Storage
            | Pragma_Time_Slice
            | Pragma_Title
            | Pragma_Unimplemented_Unit
            | Pragma_Universal_Aliasing
            | Pragma_Universal_Data
            | Pragma_Unreferenced_Objects
            | Pragma_Unreserve_All_Interrupts
            | Pragma_Use_VADS_Size
            | Pragma_Warning_As_Error
            | Pragma_Wide_Character_Encoding

         --  Group 2b - Ada RM pragmas

            | Pragma_Discard_Names
            | Pragma_Task_Dispatching_Policy
            | Pragma_All_Calls_Remote
            | Pragma_Asynchronous
            | Pragma_Remote_Call_Interface
            | Pragma_Remote_Types
            | Pragma_Shared_Passive
            | Pragma_Lock_Free
            | Pragma_Storage_Size
         =>
            return +Void;

         --  Unknown_Pragma is treated here. We use an OTHERS case in order to
         --  deal with all the more recent pragmas introduced in GNAT for which
         --  we have not yet defined how they are supported in SPARK. Do not
         --  issue a warning on unknown pragmas, as an error is issued in
         --  SPARK.Definition.

         when others =>
            return +Void;
      end case;
   end Transform_Pragma;

   ----------------------------
   -- Transform_Pragma_Check --
   ----------------------------

   procedure Transform_Pragma_Check
     (Stmt    :     Node_Id;
      Force   :     Boolean;
      Expr    : out Node_Id;
      Runtime : out W_Prog_Id;
      Pred    : out W_Pred_Id)
   is
      Arg1   : constant Node_Id := First (Pragma_Argument_Associations (Stmt));
      Arg2   : constant Node_Id := Next (Arg1);
      Params : Transformation_Params := Assert_Params;

   begin
      Expr := Expression (Arg2);

      if not Force and then Is_Ignored_Pragma_Check (Stmt) then
         Runtime := +Void;
         Pred := True_Pred;
         return;
      end if;

      if Present (Expr) then
         Runtime := +Transform_Expr (Expr, EW_Prog, Params => Params);
         Params.Gen_Marker := GM_All;
         Pred := +Transform_Expr (Expr, EW_Pred, Params => Params);
         return;
      else
         raise Program_Error;
      end if;
   end Transform_Pragma_Check;

   function Transform_Pragma_Check
     (Prag  : Node_Id;
      Force : Boolean) return W_Prog_Id
   is
      Expr       : Node_Id;
      Check_Expr : W_Prog_Id;
      Pred       : W_Pred_Id;

      --  Mark non-selected loop invariants (those not occurring
      --  next to the first batch of selected variants and
      --  invariants) as loop invariant VCs.

      Reason : constant VC_Kind :=
        (if Is_Pragma_Check (Prag, Name_Loop_Invariant)
         then VC_Loop_Invariant
         else VC_Assert);

      T : W_Prog_Id;

   begin
      --  pre / post / predicate are not handled here, unless Force is True

      if not Force and then Is_Ignored_Pragma_Check (Prag)
      then
         return +Void;
      end if;

      Transform_Pragma_Check (Prag, Force, Expr, Check_Expr, Pred);

      --  Assert_And_Cut is not handled here, except for runtime errors

      if Is_Pragma_Assert_And_Cut (Prag) then
         if Check_Expr /= Why_Empty then
            return New_Ignore (Prog => Check_Expr);
         else
            return +Void;
         end if;
      end if;

      --  Translate Compile_Time_Error as an assumption

      if Is_Pragma_Check (Prag, Name_Compile_Time_Error) then
         T :=
           Sequence (New_Assume_Statement (Pred => New_Not (Right => +Pred)),
                     Warn_On_Inconsistent_Assume (Prag));

      else
         --  Get rid of simple cases True and False

         declare
            Is_CT_Known : constant Boolean := Compile_Time_Known_Value (Expr);
         begin
            if Is_CT_Known
              or else Is_False_Boolean (+Pred)
              or else Is_True_Boolean (+Pred)
            then
               declare
                  Proved : constant Boolean :=
                    (if Is_CT_Known then Expr_Value (Expr) = Uint_1
                     else Is_True_Boolean (+Pred));
               begin
                  if Proved then
                     Emit_Static_Proof_Result
                       (Expr, Reason, Proved, Current_Subp);
                     return +Void;
                  else
                     return
                       +New_VC_Expr
                       (Ada_Node => Prag,
                        Expr     => +New_Identifier (Name => "absurd"),
                        Reason   => Reason,
                        Domain   => EW_Prog);
                  end if;
               end;
            end if;
         end;

         --  Now handle remaining cases of "regular" pragma Check/Assert
         --  and pragma Assume. This is also how pragmas Preconditions and
         --  Postconditions inside a subprogram body are translated, i.e.
         --  as regular assertions.

         if Is_Pragma_Check (Prag, Name_Assume) then
            T :=
              Sequence (New_Assume_Statement (Pred => Pred),
                        Warn_On_Inconsistent_Assume (Prag));
         else
            T := New_Located_Assert (Expr, Pred, Reason, EW_Assert);
         end if;
      end if;

      if Check_Expr /= Why_Empty then
         T := Sequence (New_Ignore (Prog => Check_Expr), T);
      end if;

      return T;
   end Transform_Pragma_Check;

   --------------------------------
   -- Transform_Priority_Pragmas --
   --------------------------------

   function Transform_Priority_Pragmas (Prag : Node_Id) return W_Prog_Id
   is
      Pragma_Arguments : constant List_Id :=
        Pragma_Argument_Associations (Prag);

      Expr : constant Node_Id :=
        (if Present (Pragma_Arguments)
         then Expression (First (Pragma_Arguments))
         else Empty);

   begin
      if Present (Expr) then
         declare
            --  Task Priorities (D.1 (17)):
            --
            --  For the Priority aspect, the value of the expression is
            --  converted to the subtype Priority; for the Interrupt_Priority
            --  aspect, this value is converted to the subtype Any_Priority.
            --
            --  Protected Subprograms (D.3 (6)):
            --
            --  The expression specified for the Priority or Interrupt_Priority
            --  aspect (see D.1) is evaluated as part of the creation of the
            --  corresponding protected object and converted to the subtype
            --  System.Any_Priority or System.Interrupt_Priority, respectively.
            --
            --  We use the Current_Subp entity to know whether the priority is
            --  a task priority or a protected priority. The priority is a task
            --  priority if it applies syntactically to a task or to a
            --  subprogram.

            Is_Task_Priority : constant Boolean :=
              Ekind (Current_Subp) in Task_Kind | Subprogram_Kind;

            Prag_Id : constant Pragma_Id := Get_Pragma_Id (Prag);

            Ty : constant Entity_Id :=
              RTE (if Is_Task_Priority
                   then
                     (if Prag_Id = Pragma_Interrupt_Priority
                      then RE_Any_Priority
                      else RE_Priority)
                   else
                     (if Prag_Id = Pragma_Interrupt_Priority
                      then RE_Interrupt_Priority
                      else RE_Any_Priority));

            Why_Expr : constant W_Expr_Id :=
              Transform_Expr
                (Expr          => Expr,
                 Domain        => EW_Term,
                 Params        => Body_Params,
                 Expected_Type => EW_Int_Type);

         begin
            return
              New_Located_Assert
                (Ada_Node => Expr,
                 Pred     =>
                   +New_Range_Expr
                     (Domain => EW_Pred,
                      Low    =>
                        New_Attribute_Expr
                          (Domain => EW_Term,
                           Ty     => Ty,
                           Attr   => Attribute_First,
                           Params => Body_Params),
                      High   =>
                        New_Attribute_Expr
                          (Domain => EW_Term,
                           Ty     => Ty,
                           Attr   => Attribute_Last,
                           Params => Body_Params),
                      Expr   => Why_Expr),
                 Reason   => VC_Range_Check,
                 Kind     => EW_Check);
         end;
      else
         return +Void;
      end if;
   end Transform_Priority_Pragmas;

   -------------------------------------
   -- Transform_Quantified_Expression --
   -------------------------------------

   function Transform_Quantified_Expression
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params)
      return W_Expr_Id
   is
      -----------------------
      -- Local Subprograms --
      -----------------------

      function Get_Expr_Quantified_Over
        (N          : Node_Id;
         Over_Range : Boolean)
         return Node_Id;
      --  @return the expression over which quantification is performed

      function Get_Quantified_Variable
        (N          : Node_Id;
         Over_Range : Boolean)
         return Entity_Id;
      --  @return the entity representing the quantified variable of the
      --     quantification.

      function Make_Binding_For_Array
        (Ada_Node    : Node_Id;
         W_Arr_Expr  : W_Expr_Id;
         W_Index_Var : W_Identifier_Id;
         W_Quant_Var : W_Identifier_Id;
         Domain      : EW_Domain)
         return W_Expr_Id;
      --  @param Ada_Node quantified expression over an array
      --  @param W_Arr_Expr Why3 expression for the array value
      --  @param W_Index_Var Why3 name for the index of the quantification
      --  @param W_Quant_Var Why3 name for the quantified variable of the
      --     quantified expression in SPARK.
      --  @return the expression that binds the value of variable [W_Quant_Var]
      --     to the value of index variable [W_Index_Var]. For example, given
      --     a quantified expression (for all E of Arr => ...) and index
      --     variable J, it returns arr(j) suitably converted to E's type.

      function Make_Binding_For_Iterable
        (Ada_Node    : Node_Id;
         W_Over_E    : W_Expr_Id;
         Over_Type   : Entity_Id;
         W_Index_Var : W_Identifier_Id;
         Domain      : EW_Domain;
         Element_T   : W_Type_Id;
         Params      : Transformation_Params)
         return W_Expr_Id;
      --  @param Ada_Node quantified expression over a container
      --  @param W_Over_E Why3 expression for the container value
      --  @param Over_Type Entity of the container type
      --  @param W_Index_Var Why3 name for the index of the quantification
      --  @param Domain domain in which the quantification is translated
      --  @param Element_T Why3 type of the Index variable
      --  @param Params transformation parameters to be used.
      --  @return the expression that should be used to bind the index of a
      --  "of" quantified expression on a type with the Iterable aspect.
      --  Returns Element (W_Over_E, W_Index_Var)

      function Make_Constraint_For_Iterable
        (Ada_Node     : Node_Id;
         Use_Contains : Boolean;
         W_Over_E     : W_Expr_Id;
         Over_Type    : Entity_Id;
         W_Index_Var  : W_Expr_Id;
         Domain       : EW_Domain;
         Params       : Transformation_Params)
         return W_Expr_Id;
      --  @param Ada_Node quantified expression over a container
      --  @param Use_Contains wether there is a Contains primitive specified
      --         for Over_Type
      --  @param W_Over_E Why3 expression for the container value
      --  @param Over_Type Entity of the container type
      --  @param W_Index_Var Why3 name for the index of the quantification
      --  @param Domain domain in which the quantification is translated
      --  @param Params transformation parameters to be used
      --  @return the expression for the constraint of a quantified
      --     expression on a type with the Iterable aspect, which is equivalent
      --     to Has_Element (W_Over_E, W_Index_Var)

      procedure Parse_Iteration_Scheme_For_Iterable
        (Ada_Node     :        Node_Id;
         Of_Present   :        Boolean;
         W_Over_E     : in out W_Expr_Id;
         Over_Type    : in out Entity_Id;
         Index_Type   :    out Entity_Id;
         Need_Tmp_Var :    out Boolean);
      --  Computes the Index_Type to be used for quantifying over Over_Type.
      --  Goes through Model functions from pragma Annotate Iterate_For_Proof
      --  and updates W_Over_E and Over_Type accordingly.
      --  @param Ada_Node quantified expression over a container
      --  @param Of_Present quantification is done over a container's content
      --  @param W_Over_E Why3 expression for the container value
      --  @param Over_Type Entity of the container type on which quantification
      --         should be done
      --  @param Index_Type type of the index variable
      --  @param Need_Tmp_Var do we need a temporary variable

      ------------------------------
      -- Get_Expr_Quantified_Over --
      ------------------------------

      function Get_Expr_Quantified_Over
        (N          : Node_Id;
         Over_Range : Boolean)
         return Node_Id
      is
      begin
         if Over_Range then
            return
              Discrete_Subtype_Definition (Loop_Parameter_Specification (N));
         else
            return Get_Container_In_Iterator_Specification
              (Iterator_Specification (N));
         end if;
      end Get_Expr_Quantified_Over;

      -----------------------------
      -- Get_Quantified_Variable --
      -----------------------------

      function Get_Quantified_Variable
        (N          : Node_Id;
         Over_Range : Boolean)
         return Entity_Id
      is
      begin
         if Over_Range then
            return Defining_Identifier (Loop_Parameter_Specification (N));
         else
            return Defining_Identifier (Iterator_Specification (N));
         end if;
      end Get_Quantified_Variable;

      ----------------------------
      -- Make_Binding_For_Array --
      ----------------------------

      function Make_Binding_For_Array
        (Ada_Node    : Node_Id;
         W_Arr_Expr  : W_Expr_Id;
         W_Index_Var : W_Identifier_Id;
         W_Quant_Var : W_Identifier_Id;
         Domain      : EW_Domain)
         return W_Expr_Id
      is
         W_Acc_Expr : constant W_Expr_Id :=
           New_Array_Access (Ada_Node => Ada_Node,
                             Domain   => Domain,
                             Ar       => W_Arr_Expr,
                             Index    => (1 => +W_Index_Var));
      begin
         return Insert_Checked_Conversion
           (Ada_Node => Ada_Node,
            Domain   => Domain,
            Expr     => W_Acc_Expr,
            To       => Get_Type (+W_Quant_Var));
      end Make_Binding_For_Array;

      -------------------------------
      -- Make_Binding_For_Iterable --
      -------------------------------

      function Make_Binding_For_Iterable
        (Ada_Node    : Node_Id;
         W_Over_E    : W_Expr_Id;
         Over_Type   : Entity_Id;
         W_Index_Var : W_Identifier_Id;
         Domain      : EW_Domain;
         Element_T   : W_Type_Id;
         Params      : Transformation_Params)
         return W_Expr_Id
      is
         Element_E   : constant Entity_Id :=
           Get_Iterable_Type_Primitive (Over_Type, Name_Element);
         Cont_Type   : constant Entity_Id :=
           Etype (First_Formal (Element_E));
         Cont_Expr   : constant W_Expr_Id :=
           Insert_Simple_Conversion
             (Domain   => Domain,
              Expr     => W_Over_E,
              To       => Type_Of_Node (Cont_Type));
         Curs_Type   : constant Entity_Id :=
           Etype (Next_Formal (First_Formal (Element_E)));
         Curs_Expr   : constant W_Expr_Id :=
           Insert_Simple_Conversion
             (Ada_Node => Empty,
              Domain   => Domain,
              Expr     => +W_Index_Var,
              To       => Type_Of_Node (Curs_Type));
      begin
         if Domain in EW_Prog | EW_Pterm then
            return New_VC_Call
              (Ada_Node => Ada_Node,
               Name     =>
                 W_Identifier_Id
                   (Transform_Identifier (Params       => Params,
                                          Expr         => Element_E,
                                          Ent          => Element_E,
                                          Domain       => Domain)),
               Progs    => (1 => Cont_Expr,
                            2 => Curs_Expr),
               Reason   => VC_Precondition,
               Domain   => Domain,
               Typ      => Element_T);
         else
            return New_Function_Call
              (Ada_Node => Ada_Node,
               Name     =>
                 W_Identifier_Id
                   (Transform_Identifier (Params       => Params,
                                          Expr         => Element_E,
                                          Ent          => Element_E,
                                          Domain       => Domain)),
               Subp     => Element_E,
               Args     => (1 => Cont_Expr,
                            2 => Curs_Expr),
               Domain   => Domain,
               Typ      => Element_T);
         end if;
      end Make_Binding_For_Iterable;

      ----------------------------------
      -- Make_Constraint_For_Iterable --
      ----------------------------------

      function Make_Constraint_For_Iterable
        (Ada_Node     : Node_Id;
         Use_Contains : Boolean;
         W_Over_E     : W_Expr_Id;
         Over_Type    : Entity_Id;
         W_Index_Var  : W_Expr_Id;
         Domain       : EW_Domain;
         Params       : Transformation_Params)
         return W_Expr_Id
      is
         Has_Element : Entity_Id;

      begin
         --  Look for the function that should be called to make the constraint
         --  over W_Index_Var.

         --  If there is no Contains annotation to use, use the Has_Element
         --  function of the Iterable aspect.

         if not Use_Contains then
            Has_Element := Get_Iterable_Type_Primitive
              (Over_Type, Name_Has_Element);

         --  A Contains Iterable_For_Proof annotation is specified for
         --  Over_Type. Use the provided Contains primitive.

         else
            declare
               Found         : Boolean;
               Iterable_Info : Iterable_Annotation;
            begin
               Retrieve_Iterable_Annotation (Over_Type, Found, Iterable_Info);
               pragma Assert (Found and then Iterable_Info.Kind = Contains);
               Has_Element := Iterable_Info.Entity;
            end;
         end if;

         --  Call the function with the appropriate arguments

         declare
            Subdomain   : constant EW_Domain :=
              (if Domain = EW_Pred then EW_Term else Domain);
            Cont_Type   : constant Entity_Id :=
              Etype (First_Formal (Has_Element));
            Cont_Expr   : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain   => Subdomain,
                 Expr     => W_Over_E,
                 To       => Type_Of_Node (Cont_Type));
            Curs_Type   : constant Entity_Id :=
              Etype (Next_Formal (First_Formal (Has_Element)));
            Curs_Expr   : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Ada_Node => Empty,
                 Domain   => Subdomain,
                 Expr     => +W_Index_Var,
                 To       => Type_Of_Node (Curs_Type));
            T           : W_Expr_Id;

         begin
            if Domain in EW_Prog | EW_Pterm then
               T := New_VC_Call
                 (Ada_Node => Ada_Node,
                  Name     =>
                    W_Identifier_Id
                      (Transform_Identifier (Params => Params,
                                             Expr   => Has_Element,
                                             Ent    => Has_Element,
                                             Domain => Subdomain)),
                  Progs    => (1 => Cont_Expr,
                               2 => Curs_Expr),
                  Reason   => VC_Precondition,
                  Domain   => Subdomain,
                  Typ      => Type_Of_Node (Etype (Has_Element)));
            else
               T := New_Function_Call
                 (Ada_Node => Ada_Node,
                  Name     =>
                    W_Identifier_Id
                      (Transform_Identifier (Params => Params,
                                             Expr   => Has_Element,
                                             Ent    => Has_Element,
                                             Domain => Subdomain)),
                  Subp     => Has_Element,
                  Args     => (1 => Cont_Expr,
                               2 => Curs_Expr),
                  Domain   => Subdomain,
                  Typ      => Type_Of_Node (Etype (Has_Element)));
            end if;

            return T;
         end;
      end Make_Constraint_For_Iterable;

      -----------------------------------------
      -- Parse_Iteration_Scheme_For_Iterable --
      -----------------------------------------

      procedure Parse_Iteration_Scheme_For_Iterable
        (Ada_Node     :        Node_Id;
         Of_Present   :        Boolean;
         W_Over_E     : in out W_Expr_Id;
         Over_Type    : in out Entity_Id;
         Index_Type   :    out Entity_Id;
         Need_Tmp_Var :    out Boolean)
      is
         Subdomain     : constant EW_Domain :=
           (if Domain = EW_Pred then EW_Term else Domain);
         Found         : Boolean;
         Iterable_Info : Iterable_Annotation;

      begin
         --  for ... in quantification:
         --  Iteration is done on cursors, no need for a temporary variable.

         if not Of_Present then
            Index_Type := Get_Cursor_Type (Over_Type);
            Need_Tmp_Var := False;

         --  for ... of quantification:
         --  Check wether an Iterable_For_Proof annotation is recorded for
         --  Over_Type.

         else
            Retrieve_Iterable_Annotation (Over_Type, Found, Iterable_Info);

            --  Go through Model Iterable_For_Proof annotations to find the
            --  type on which quantification should be done.

            while Found
              and then Iterable_Info.Kind = SPARK_Definition.Annotate.Model
            loop
               --  Replace W_Over_E by Model (W_Over_E) and Over_Type by the
               --  model's type.

               declare
                  Model     : constant Entity_Id := Iterable_Info.Entity;
                  Cont_Type : constant Entity_Id :=
                    Etype (First_Formal (Model));
                  Cont_Expr : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain   => Subdomain,
                       Expr     => W_Over_E,
                       To       => Type_Of_Node (Cont_Type));
               begin
                  Over_Type := Etype (Model);
                  if Subdomain = EW_Term then
                     W_Over_E := New_Function_Call
                       (Ada_Node => Ada_Node,
                        Name     =>
                          W_Identifier_Id
                            (Transform_Identifier (Params => Params,
                                                   Expr   => Model,
                                                   Ent    => Model,
                                                   Domain => Subdomain)),
                        Subp     => Model,
                        Args     => (1 => Cont_Expr),
                        Domain   => Subdomain,
                        Typ      => Type_Of_Node (Over_Type));
                  else
                     W_Over_E := New_VC_Call
                       (Ada_Node => Ada_Node,
                        Name     =>
                          W_Identifier_Id
                            (Transform_Identifier (Params => Params,
                                                   Expr   => Model,
                                                   Ent    => Model,
                                                   Domain => Subdomain)),
                        Progs    => (1 => Cont_Expr),
                        Reason   => VC_Precondition,
                        Domain   => Subdomain,
                        Typ      => Type_Of_Node (Over_Type));
                  end if;
               end;

               Retrieve_Iterable_Annotation (Over_Type, Found, Iterable_Info);
            end loop;

            --  No Contains Iterable_For_Proof annotation found.
            --  Iteration is done on cursors, we need a temporary variable
            --  to store the element.

            if not Found then
               Index_Type := Get_Cursor_Type (Over_Type);
               Need_Tmp_Var := True;

            --  A Contains Iterable_For_Proof annotation has been found.
            --  Iteration is directly done on elements, no need for a
            --  temporary variable.

            else
               Index_Type :=
                 Etype (Get_Iterable_Type_Primitive (Over_Type, Name_Element));

               Need_Tmp_Var := False;
            end if;
         end if;
      end Parse_Iteration_Scheme_For_Iterable;

      ---------------------
      -- Local Variables --
      ---------------------

      --  We distinguish between 4 types of quantified expressions:
      --  . over a scalar range (for all V in Low .. High)
      --  . over an array (for all V of Arr)
      --  . over a container's content (for all V of Cont)
      --  . over a container's cursors (for all V in Cont)
      --  The boolean variables below correspond to these 4 mutually exclusive
      --  cases.

      Over_Range : constant Boolean :=
        Present (Loop_Parameter_Specification (Expr));

      Over_Array : constant Boolean :=
        Present (Iterator_Specification (Expr))
          and then Is_Iterator_Over_Array (Iterator_Specification (Expr));

      Over_Content : constant Boolean :=
        Present (Iterator_Specification (Expr))
          and then not Over_Array
          and then Of_Present (Iterator_Specification (Expr));

      Over_Cursors : constant Boolean :=
        Present (Iterator_Specification (Expr))
          and then not Over_Array
          and then not Over_Content;

      --  We distinguish the quantified variable from the index variable in our
      --  translation. For quantifications over a scalar range, they are the
      --  same. For quantifications over an array or a container of the form
      --  (for V of E) the quantified variable is V, and the index variable is
      --  the variable over which quantification is done in Why3, over the
      --  underlying scalar range for array/container E.

      Need_Temp_Var : Boolean; --  Index variable is not quantified variable

      Quant_Var  : Entity_Id;  --  Quantified variable for quantification
      Over_Expr  : Node_Id;    --  Expression over which quantification is done
      Over_Type  : Node_Id;    --  Type used for the quantification
      Quant_Type : Entity_Id;  --  Type of the quantified variable
      Index_Type : Entity_Id;  --  Index type for the quantification

      W_Quant_Type : W_Type_Id;  --  Why3 type for the quantified variable
      W_Index_Type : W_Type_Id;  --  Why3 type for the index variable

      W_Over_Expr  : W_Expr_Id;  --  Why3 expression for the expression over
                                 --  which quantification is done. This is only
                                 --  used in those cases where the quantified
                                 --  and the index variables are not the same,
                                 --  thus needing binding between the two that
                                 --  relies on this expression.
      W_Bound_Expr : W_Expr_Id;  --  Why3 expression for the constraint giving
                                 --  the bounds over which quantification is
                                 --  done.
      Result       : W_Expr_Id;  --  Why3 expression for the quantification

      W_Quant_Var  : W_Identifier_Id;  --  Why3 name for the quantified
                                       --  variable.
      W_Index_Var  : W_Identifier_Id;  --  Why3 name for the index variable

   --  Start of processing for Transform_Quantified_Expression

   begin
      --  The usual translation of quantified expression into Why3 is as a
      --  predicate (Domain = EW_Pred), into a forall or exists quantification
      --  in Why3. For programs (Domain = EW_Prog), we also need to check the
      --  absence of run-time errors in sub-expressions. The case of terms
      --  (Domain in EW_Terms) appears when the quantified expression needs
      --  to be considered of type bool in Why3, for example because it is
      --  assigned into a Boolean variable in SPARK. In this case, we transform
      --  the quantified expression into a predicate, and convert this
      --  predicate (pred) into a term (if pred then True else False).

      if Domain in EW_Terms then
         declare
            Pred : constant W_Expr_Id :=
              Transform_Quantified_Expression (Expr, EW_Pred, Params);
         begin
            return Boolean_Expr_Of_Pred (+Pred, Domain);
         end;
      end if;

      --  Domain = EW_Pred or Domain = EW_Prog

      --  Step 1: create a Why3 variable for the quantified variable

      Over_Expr := Get_Expr_Quantified_Over (Expr, Over_Range);
      Quant_Var  := Get_Quantified_Variable (Expr, Over_Range);
      Quant_Type := Etype (Quant_Var);

      W_Quant_Type := (if Use_Split_Form_For_Type (Quant_Type)
                       then EW_Split (Quant_Type)
                       else Type_Of_Node (Quant_Type));

      --  In case of a for of quantification, the quantified variable may be
      --  partially initialized if it is not a scalar type and:
      --  * the quantification is done on an array with relaxed initialization
      --  * the quantification is done on a container and the Element function
      --    returns a partially intialized expression.
      --  ??? for now we only check the return type to decide if we are in the
      --  second case.

      if (Over_Array
          and then (Expr_Has_Relaxed_Init (Over_Expr)
                    or else Has_Relaxed_Init (Quant_Type))
          and then not Has_Scalar_Type (Quant_Type))
        or else (Over_Content
                 and then Has_Relaxed_Init (Quant_Type)
                 and then not Has_Scalar_Type (Quant_Type))
      then
         W_Quant_Type := EW_Init_Wrapper (W_Quant_Type);
      end if;

      W_Quant_Var := New_Identifier (Name => Short_Name (Quant_Var),
                                     Typ  => W_Quant_Type);

      --  Step 2: translate the expression over which the quantification is
      --          applied.

      if not Over_Range then
         Over_Type := Etype (Over_Expr);
      else
         Over_Type := Empty;
      end if;

      if not Over_Range then
         W_Over_Expr :=
           Transform_Expr
             (Over_Expr, Prog_Or_Term_Domain (Domain), Params);
      else
         W_Over_Expr := Why_Empty;  --  safe assignment in the unused case
      end if;

      --  Step 3: parse the iteration scheme to compute the proper Index_Type.
      --          When the quantification is done over a container, also
      --          update Over_Type and W_Over_Expr to go through model
      --          functions when one is specified using pragma Annotate
      --          Iterate_For_Proof.

      if Over_Array then
         Need_Temp_Var := True;
         Index_Type := Etype (First_Index (Etype (Over_Expr)));

      elsif Over_Range then
         Need_Temp_Var := False;
         Index_Type := Quant_Type;

      else
         pragma Assert (Over_Content or Over_Cursors);

         Parse_Iteration_Scheme_For_Iterable
           (Ada_Node     => Expr,
            Of_Present   => Over_Content,
            W_Over_E     => W_Over_Expr,
            Over_Type    => Over_Type,
            Index_Type   => Index_Type,
            Need_Tmp_Var => Need_Temp_Var);
      end if;

      if Need_Temp_Var then
         W_Index_Type := (if Use_Split_Form_For_Type (Index_Type)
                          then Base_Why_Type (Index_Type)
                          else Type_Of_Node (Index_Type));
         W_Index_Var := New_Temp_Identifier (Typ => W_Index_Type);
      else
         W_Index_Type := W_Quant_Type;
         W_Index_Var := W_Quant_Var;
      end if;

      --  Save W_Over_Expr in a temporary, which can then be referred to in any
      --  context (including predicates even when Domain = EW_Prog), which
      --  requires that the expression is first evaluated in the appropriate
      --  context to possibly generate run-time checks

      if not Over_Range then
         W_Over_Expr := New_Temp_For_Expr (W_Over_Expr);
      end if;

      --  Step 4: translate the constraints over the index variable

      if Over_Range or Over_Array then

         if Over_Array then
            W_Bound_Expr :=
              New_Array_Range_Expr (+W_Index_Var, W_Over_Expr, Domain, 1);
         else
            W_Bound_Expr :=
              Range_Expr (Over_Expr, +W_Index_Var, Domain, Params);
         end if;

      else
         pragma Assert (Over_Content or Over_Cursors);

         --  Call the appropriate primitive

         W_Bound_Expr :=
           +Make_Constraint_For_Iterable
           (Ada_Node     => Expr,
            Use_Contains => Over_Content and then not Need_Temp_Var,
            W_Over_E     => W_Over_Expr,
            Over_Type    => Over_Type,
            W_Index_Var  => +W_Index_Var,
            Domain       => Domain,
            Params       => Params);

         --  Add the dynamic predicate of the index type
         --  It will be needed to use Has_Element definition.

         declare
            Inv : constant W_Pred_Id := Compute_Dynamic_Invariant
              (Expr          => +W_Index_Var,
               Ty            => Index_Type,
               Initialized   => True_Term,
               Only_Var      => False_Term,
               Params        => Params);
         begin
            W_Bound_Expr :=
              New_And_Expr
                (Left   => Boolean_Expr_Of_Pred (+Inv, Domain),
                 Right  => W_Bound_Expr,
                 Domain => Domain);
         end;
      end if;

      --  Step 5: translate the condition in the quantified expression, in a
      --          context where the quantified variable is known.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      Insert_Entity (Quant_Var, W_Quant_Var);
      Result := Transform_Expr (Condition (Expr), Domain, Params);
      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      --  Step 6: in those cases where the quantified variable and the index
      --          variable are not the same, wrap the result in an expression
      --          that gives a value to the quantified variable based on the
      --          value of the index variable.

      if Need_Temp_Var then
         declare
            W_Binding_Expr : W_Expr_Id;
         begin
            if Over_Array then
               W_Binding_Expr :=
                 Make_Binding_For_Array
                   (Expr, W_Over_Expr, W_Index_Var, W_Quant_Var,
                    Prog_Or_Term_Domain (Domain));
            else
               pragma Assert (Over_Content or Over_Cursors);
               W_Binding_Expr :=
                 Make_Binding_For_Iterable
                   (Expr, W_Over_Expr, Over_Type, +W_Index_Var,
                    Prog_Or_Term_Domain (Domain), W_Quant_Type, Params);
            end if;

            Result := New_Typed_Binding (Domain  => Domain,
                                         Name    => W_Quant_Var,
                                         Def     => W_Binding_Expr,
                                         Context => Result);
         end;
      end if;

      --  Step 7: translate the quantified expression into a quantification in
      --          the predicate case, and an 'any' expression with a
      --          postcondition that uses the translation to predicate in the
      --          program case.

      if Domain = EW_Pred then
         declare
            Connector  : constant EW_Connector :=
              (if All_Present (Expr) then EW_Imply else EW_And);
            Quant_Body : constant W_Pred_Id :=
              New_Connection (Op    => Connector,
                              Left  => W_Bound_Expr,
                              Right => Result);
         begin
            if All_Present (Expr) then
               Result :=
                  New_Universal_Quantif
                     (Ada_Node  => Expr,
                      Variables => (1 => W_Index_Var),
                      Labels    =>
                        Get_Counterexample_Labels
                          (Quant_Var,

                           --  When quantification is done on a temporary
                           --  variable, append a fake 'Index attribute that
                           --  will be recognized in counterexample handling.

                           Append_To_Name =>
                             (if Need_Temp_Var then "'" & Index_Label
                              else "")),
                      Var_Type  => W_Index_Type,
                      Pred      => Quant_Body);
            else
               Result :=
                  New_Existential_Quantif
                     (Ada_Node  => Expr,
                      Variables => (1 => W_Index_Var),
                      Labels    => Symbol_Sets.Empty_Set,
                      Var_Type  => W_Index_Type,
                      Pred      => Quant_Body);
            end if;
         end;

      --  We are interested in the checks for the entire range, and in the
      --  return value of the entire expression, but we are not interested in
      --  the exact order in which things are evaluated. We also do not want
      --  to translate the expression function by a loop. So our scheme is:
      --    for all I in Cond => Expr
      --
      --  becomes:
      --    (let i = ref [ int ] in
      --       if cond then ignore (expr));
      --    [ { } bool { result = true <-> expr } ]
      --  The condition is a formula that expresses that i is in the range
      --  given by the quantification.

      else  --  Domain = EW_Prog
         declare
            --  Possibly warn on an unreachable quantified expression

            W_Result      : constant W_Prog_Id := New_Ignore (Prog => +Result);
            W_Wrap_Result : constant W_Expr_Id :=
              Warn_On_Dead_Branch (Condition (Expr), +W_Result, Params.Phase);
            W_RTE : constant W_Prog_Id :=
              +New_Typed_Binding
                (Name    => W_Index_Var,
                 Domain  => EW_Prog,
                 Def     => +New_Simpl_Any_Prog (W_Index_Type),
                 Context =>
                   New_Conditional
                     (Domain    => EW_Prog,
                      Condition => W_Bound_Expr,
                      Then_Part => W_Wrap_Result));
            W_Expr_Pred : constant W_Expr_Id :=
              Transform_Expr (Expr, EW_Pred, Params);
            W_Equiv : constant W_Expr_Id :=
              New_Connection
                (Domain   => EW_Pred,
                 Left     =>
                   New_Call (Domain => EW_Pred,
                             Name   => Why_Eq,
                             Typ    => EW_Bool_Type,
                             Args   => (+New_Result_Ident (EW_Bool_Type),
                                        +True_Term)),
                 Op       => EW_Equivalent,
                 Right    => W_Expr_Pred);
            W_Assume : constant W_Prog_Id :=
              New_Any_Statement (Ada_Node    => Expr,
                                 Return_Type => EW_Bool_Type,
                                 Post        => +W_Equiv);
         begin
            Result := +Sequence (W_RTE, W_Assume);
         end;
      end if;

      --  Step 8: possibly bind the value of the temporary introduced for
      --          the expression over which quantification is done.

      if not Over_Range then
         Result := Binding_For_Temp (Ada_Node => Expr,
                                     Domain   => Domain,
                                     Tmp      => W_Over_Expr,
                                     Context  => Result);
      end if;

      return Result;
   end Transform_Quantified_Expression;

   ---------------------------------------------
   -- Transform_Record_Component_Associations --
   ---------------------------------------------

   function Transform_Record_Component_Associations
     (Domain             : EW_Domain;
      Typ                : Entity_Id;
      Assocs             : List_Id;
      Params             : Transformation_Params;
      In_Delta_Aggregate : Boolean := False;
      Init_Wrapper       : Boolean) return W_Field_Association_Array
   is
      function Components_Count (Assocs : List_Id) return Natural;
      --  Returns the number of component selectors in Assocs

      ----------------------
      -- Components_Count --
      ----------------------

      function Components_Count (Assocs : List_Id) return Natural is
         CL          : List_Id;
         Association : Node_Id := Nlists.First (Assocs);
         Associated_Components : Natural := 0;
      begin
         while Present (Association) loop
            if not Inherited_Discriminant (Association) then
               CL := Choices (Association);
               Associated_Components := Associated_Components +
                 Integer (List_Length (CL));
            end if;
            Next (Association);
         end loop;
         return Associated_Components;
      end Components_Count;

      Component   : Entity_Id;
      Association : Node_Id;
      Field_Assoc :
        W_Field_Association_Array (1 .. Components_Count (Assocs));
      Num_Discr   : constant Integer := Count_Discriminants (Typ);
      Discr_Assoc :
        W_Field_Association_Array (1 .. Num_Discr);
      Result      :
        W_Field_Association_Array (1 .. Components_Count (Assocs));
      Field_Index : Positive := 1;
      Discr_Index : Positive := 1;
      CL          : List_Id;
      Choice      : Node_Id;

   --  Start of processing for Transform_Record_Component_Associations

   begin
      Association := Nlists.First (Assocs);

      if No (Association) then
         return (1 .. 0 => <>);
      end if;

      --  Start with the first component
      CL := Choices (Association);
      --  normal, fully defined aggregate, has singleton choice lists
      pragma Assert (In_Delta_Aggregate or else List_Length (CL) = 1);
      Choice := First (CL);

      --  Loop over the associations and component choice lists
      while Present (Choice) loop
         declare
            Expr : W_Expr_Id;
         begin
            --  We don't expect "others" for delta aggregates (illegal). For
            --  normal aggregates occurances of "others" have been removed from
            --  the AST wich will have an association list is as long as the
            --  number of components, and with only singleton choice lists.

            pragma Assert (Nkind (Choice) /= N_Others_Choice);

            --  Inherited discriminants in an extension aggregate are already
            --  accounted for in the ancestor part. Ignore them here.

            if not Inherited_Discriminant (Association) then

               --  Use Entity link to get the corresponding record component

               pragma Assert (Present (Entity (Choice)));

               Component := Search_Component_In_Type (Typ, Entity (Choice));
               pragma Assert (Present (Component));

               if not Box_Present (Association) then
                  Expr := Transform_Expr
                    (Expr          => Expression (Association),
                     Expected_Type =>
                       EW_Abstract
                         (Etype (Component),
                          Relaxed_Init =>
                            (Init_Wrapper
                             or else Has_Relaxed_Init (Etype (Component)))
                          and then Ekind (Component) = E_Component),
                     Domain        => Domain,
                     Params        => Params);
               else
                  pragma Assert (Domain = EW_Prog);
                  Expr := +New_Simpl_Any_Prog
                    (T =>
                       EW_Abstract
                         (Etype (Component),
                          Relaxed_Init =>
                            (Init_Wrapper
                             or else Has_Relaxed_Init (Etype (Component)))
                          and then Ekind (Component) = E_Component));
               end if;

               --  Attributes of component's type have default values of their
               --  type.

               if Has_Record_Type (Etype (Component))
                 or else Full_View_Not_In_SPARK (Etype (Component))
               then
                  Expr := New_Tag_Update
                    (Domain   => Domain,
                     Name     => Expr,
                     Ty       => Etype (Component));
               end if;

               if Ekind (Component) = E_Discriminant then
                  Discr_Assoc (Discr_Index) := New_Field_Association
                    (Domain => Domain,
                     Field  => To_Why_Id
                       (Component, Rec => Root_Retysp (Typ)),
                     Value  => Expr);
                  Discr_Index := Discr_Index + 1;
               else
                  Field_Assoc (Field_Index) := New_Field_Association
                    (Domain => Domain,
                     Field  => To_Why_Id
                       (Component, Rec => Typ, Relaxed_Init => Init_Wrapper),
                     Value  => Expr);
                  Field_Index := Field_Index + 1;
               end if;
            end if;

            --  Getting the next component from the associations' component
            --  lists, which may require selecting the next choice (for
            --  delta aggregates), or selecting the next component association.

            Next (Choice);
            if No (Choice) then
               Next (Association);
               if Present (Association) then
                  CL := Choices (Association);
                  pragma Assert (In_Delta_Aggregate
                                  or else List_Length (CL) = 1);
                  Choice := First (CL);
               end if;
            end if;
         end;
      end loop;

      pragma Assert (No (Association));
      pragma Assert
        ((In_Delta_Aggregate and then Field_Index = Result'Last + 1)
         or else Is_Tagged_Type (Typ)
         or else Discr_Index = Discr_Assoc'Last + 1);
      Result := Discr_Assoc (1 .. Discr_Index - 1) &
        Field_Assoc (1 .. Field_Index - 1);
      return Result;
   end Transform_Record_Component_Associations;

   ------------------------------------
   -- Transform_Shift_Or_Rotate_Call --
   ------------------------------------

   function Transform_Shift_Or_Rotate_Call
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
      --  Define a convenient short hand for the test below
      function ECI (Left, Right : String) return Boolean
        renames Ada.Strings.Equal_Case_Insensitive;

      Subp        : constant Entity_Id := Entity (SPARK_Atree.Name (Expr));
      Context     : Ref_Context;
      Store       : constant W_Statement_Sequence_Unchecked_Id :=
        New_Unchecked_Statement_Sequence;

      Args        : constant W_Expr_Array :=
        Compute_Call_Args (Expr, Domain, Context, Store, Params);
      pragma Assert (Args'Length = 2);
      pragma Assert (Context.Length = 0);

      Modulus_Val : constant Uint := Modulus (Etype (Subp));
      Nb_Of_Bits  : constant Int := (if Modulus_Val = UI_Expon (2, 8) then
                                        8
                                     elsif Modulus_Val = UI_Expon (2, 16) then
                                        16
                                     elsif Modulus_Val = UI_Expon (2, 32) then
                                        32
                                     elsif Modulus_Val = UI_Expon (2, 64) then
                                        64
                                     else
                                        raise Program_Error);
      Typ         : constant W_Type_Id := (if Nb_Of_Bits = 8 then
                                              EW_BitVector_8_Type
                                           elsif Nb_Of_Bits = 16 then
                                              EW_BitVector_16_Type
                                           elsif Nb_Of_Bits = 32 then
                                              EW_BitVector_32_Type
                                           elsif Nb_Of_Bits = 64 then
                                              EW_BitVector_64_Type
                                           else raise Program_Error);
      T           : W_Expr_Id;

   begin
      --  ??? it is assumed that rotate calls are only valid on actual
      --  unsigned_8/16/32/64 types with the corresponding 'Size

      Get_Unqualified_Decoded_Name_String (Chars (Subp));

      declare
         Arg1   : constant W_Expr_Id := Args (Args'First);
         Arg2   : constant W_Expr_Id := Args (Args'First + 1);
         Arg2_M : constant W_Expr_Id :=
           Insert_Simple_Conversion (Domain => EW_Term,
                                     Expr   => Arg2,
                                     To     => Typ);
         Name_S : constant String    := Name_Buffer (1 .. Name_Len);
         Name   : constant W_Identifier_Id :=
           (if ECI (Name_S, Get_Name_String (Name_Shift_Right)) then
               MF_BVs (Typ).Lsr
            elsif ECI (Name_S, Get_Name_String (Name_Shift_Right_Arithmetic))
            then
               MF_BVs (Typ).Asr
            elsif ECI (Name_S, Get_Name_String (Name_Shift_Left)) then
               MF_BVs (Typ).Lsl
            elsif ECI (Name_S, Get_Name_String (Name_Rotate_Left)) then
               MF_BVs (Typ).Rotate_Left
            elsif ECI (Name_S, Get_Name_String (Name_Rotate_Right)) then
               MF_BVs (Typ).Rotate_Right
            else
               raise Program_Error);
         --         function Actual_Call (Amount : W_Expr_Id) return W_Expr_Id
      begin

         --  A special care need to be put in the case of shifts on a bitvector
         --  of size smaller than 32. Indeed, in this case the amount of
         --  the shift can be greater than 2**(Size of the underlying bv),
         --  resulting in a modulo on the amount of the shift Introduced by
         --  the conversion at the why3 level.
         if Nb_Of_Bits < 32
           and then Name /= MF_BVs (Typ).Rotate_Left
           and then Name /= MF_BVs (Typ).Rotate_Right
         then
            declare
               Nb_Of_Buits_UI : constant Uint := UI_From_Int (Nb_Of_Bits);
            begin
               T := New_Conditional
                 (Ada_Node  => Expr,
                  Domain    => EW_Term,
                  Condition => New_Call
                    (Domain => Domain,
                     Name   => Int_Infix_Lt,
                     Args   => (1 => Arg2,
                                2 => New_Integer_Constant
                                  (Value => Nb_Of_Buits_UI)),
                     Typ    => EW_Bool_Type),
                  Then_Part => New_Call
                       (Domain => EW_Term,
                        Name   => Name,
                        Args   =>
                          (1 => Arg1,
                           2 => Arg2_M),
                        Typ    => Typ),
                  Else_Part =>
                    New_Modular_Constant (Value => Uint_0,
                                          Typ => Typ),
                  Typ       => Typ);
            end;
         else
            T := New_Call
              (Domain => EW_Term,
               Name   => Name,
               Args   => (1 => Arg1,
                          2 => Arg2_M),
               Typ    => Typ);
         end if;
      end;

      return T;
   end Transform_Shift_Or_Rotate_Call;

   ---------------------
   -- Transform_Slice --
   ---------------------

   function Transform_Slice
     (Params       : Transformation_Params;
      Domain       : EW_Domain;
      Expr         : Node_Id) return W_Expr_Id
   is

      Prefx     : constant Node_Id := SPARK_Atree.Prefix (Expr);
      Target_Ty : constant W_Type_Id :=
        EW_Abstract
          (Etype (Expr), Relaxed_Init => Expr_Has_Relaxed_Init (Expr));
      Rng       : constant Node_Id := Get_Range (Discrete_Range (Expr));
      Pref_Expr : W_Expr_Id;
      T         : W_Expr_Id;
      Rng_Type  : constant W_Type_Id :=
        Base_Why_Type_No_Bool (Entity_Id'(Type_Of_Node (Low_Bound (Rng))));
      Low_Expr  : constant W_Expr_Id :=
        New_Temp_For_Expr
          (Transform_Expr (Low_Bound (Rng),
           Rng_Type,
           Domain,
           Params));
      High_Expr  : constant W_Expr_Id :=
        New_Temp_For_Expr
          (Transform_Expr (High_Bound (Rng),
           Rng_Type,
           Domain,
           Params));

   begin
      --  We start by translating the prefix itself

      Pref_Expr := Transform_Expr (Prefx, Domain, Params);
      Pref_Expr := New_Temp_For_Expr (Pref_Expr);
      T := Pref_Expr;

      --  if needed, we convert the arrray to a simple base type

      if not Is_Static_Array_Type (Etype (Expr))
        and then
          not Is_Static_Array_Type (Get_Ada_Node (+Get_Type (Pref_Expr)))
        and then Get_Type_Kind (Get_Type (Pref_Expr)) /= EW_Split
      then
         T := Array_Convert_To_Base (Domain, T);
      end if;

      --  if needed, we insert a check that the slice bounds are in the bounds
      --  of the prefix

      if Domain = EW_Prog then
         declare
            Ar_Low  : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain => EW_Pred,
                 To     => Rng_Type,
                 Expr   => Get_Array_Attr (Domain => EW_Pred,
                                           Expr   => Pref_Expr,
                                           Attr   => Attribute_First,
                                           Dim    => 1));
            Ar_High : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain => EW_Pred,
                 To     => Rng_Type,
                 Expr   => Get_Array_Attr (Domain => EW_Pred,
                                           Expr   => Pref_Expr,
                                           Attr   => Attribute_Last,
                                           Dim    => 1));
            Check   : constant W_Pred_Id :=
              New_Connection
                (Op    => EW_Imply,
                 Left  =>
                   New_Call
                     (Domain => EW_Pred,
                      Name   => (if Rng_Type = EW_Int_Type then
                                    Int_Infix_Le
                                 else
                                    MF_BVs (Rng_Type).Ule),
                      Typ    => EW_Bool_Type,
                      Args   => (+Low_Expr, +High_Expr)),
                 Right =>
                   New_And_Then_Expr
                     (Domain => EW_Pred,
                      Left   =>
                        New_Range_Expr
                          (Domain => EW_Pred,
                           Low    => +Ar_Low,
                           High   => +Ar_High,
                           Expr   => Low_Expr),
                      Right =>
                        New_Range_Expr
                          (Domain => EW_Pred,
                           Low    => +Ar_Low,
                           High   => +Ar_High,
                           Expr   => +High_Expr)));
         begin
            T :=
              +Sequence (New_Located_Assert (Expr,
                         Check,
                         VC_Range_Check,
                         EW_Assert),
                         +T);
         end;
      end if;

      if Is_Static_Array_Type (Etype (Expr)) then

         --  a conversion may be needed to the target type

         T :=
           Insert_Array_Conversion
             (Domain         => Domain,
              Expr           => T,
              To             => Target_Ty,
              Force_No_Slide => True);

      --  when the slice bounds are not static, we produce a compound object
      --  contents + bounds.

      else
         T :=
           Array_Convert_From_Base
             (Domain => Domain,
              Ar     => T,
              Ty     => Get_Ada_Node (+Target_Ty),
              First  => Low_Expr,
              Last   => High_Expr);
      end if;

      T :=
        Binding_For_Temp
          (Domain  => Domain,
           Tmp     => Pref_Expr,
           Context => T);
      T :=
        Binding_For_Temp
          (Domain  => Domain,
           Tmp     => Low_Expr,
           Context => T);
      T :=
        Binding_For_Temp
          (Domain  => Domain,
           Tmp     => High_Expr,
           Context => T);

      if Domain = EW_Prog
        and then Nkind (Discrete_Range (Expr)) = N_Subtype_Indication
      then
         T := +Sequence
           (Ada_Node => Expr,
            Left     => +Check_Scalar_Range
              (Params => Params,
               N      => Get_Range (Discrete_Range (Expr)),
               Base   => Entity (Subtype_Mark (Discrete_Range (Expr)))),
            Right    => +T);
      end if;

      return T;
   end Transform_Slice;

   ----------------------------------------
   -- Transform_Statement_Or_Declaration --
   ----------------------------------------

   function Transform_Statement_Or_Declaration
     (Stmt_Or_Decl        : Node_Id;
      Assert_And_Cut_Expr : out Node_Id;
      Assert_And_Cut      : out W_Pred_Id)
      return W_Prog_Id
   is

      function Havoc_Borrowed_On_Goto return W_Prog_Id;
      --  Havoc the local borrowers declared in blocks traversed by a goto
      --  statement.

      function Havoc_Borrowed_On_Return return W_Prog_Id;
      --  Havoc the local borrowers declared in blocks traversed by a return
      --  statement.

      ----------------------------
      -- Havoc_Borrowed_On_Goto --
      ----------------------------

      function Havoc_Borrowed_On_Goto return W_Prog_Id is
         Enclosing_Stmt : constant Node_Id :=
           Statement_Enclosing_Label (Entity (Name (Stmt_Or_Decl)));

         function Is_Scop_Or_Block (N : Node_Id) return Boolean is
           (Nkind (N) = N_Block_Statement or else N = Enclosing_Stmt);

         function Enclosing_Block_Stmt is new
           First_Parent_With_Property (Is_Scop_Or_Block);

         Scop : Node_Id := Stmt_Or_Decl;
         Res  : W_Prog_Id := +Void;
      begin
         loop
            Scop := Enclosing_Block_Stmt (Scop);
            exit when Scop = Enclosing_Stmt;
            Res := Sequence (Res, +Havoc_Borrowed_From_Block (Scop));
         end loop;
         return Res;
      end Havoc_Borrowed_On_Goto;

      ------------------------------
      -- Havoc_Borrowed_On_Return --
      ------------------------------

      function Havoc_Borrowed_On_Return return W_Prog_Id is
         function Is_Body_Or_Block (N : Node_Id) return Boolean is
           (Nkind (N) in N_Block_Statement
                       | N_Entity_Body);

         function Enclosing_Block_Stmt is new
           First_Parent_With_Property (Is_Body_Or_Block);

         Scop : Node_Id := Stmt_Or_Decl;
         Res  : W_Prog_Id := +Void;
      begin
         loop
            Scop := Enclosing_Block_Stmt (Scop);
            exit when Nkind (Scop) /= N_Block_Statement;
            Res := Sequence (Res, +Havoc_Borrowed_From_Block (Scop));
         end loop;
         return Res;
      end Havoc_Borrowed_On_Return;

   --  Start of processing for Transform_Statement_Or_Declaration

   begin
      --  Make sure that outputs are initialized

      Assert_And_Cut_Expr := Empty;
      Assert_And_Cut := Why_Empty;

      --  Set error node so that bugbox information will be correct

      Current_Error_Node := Stmt_Or_Decl;

      case Nkind (Stmt_Or_Decl) is
         when N_Ignored_In_SPARK =>
            return +Void;

         when N_Assignment_Statement =>
            return Transform_Assignment_Statement (Stmt_Or_Decl);

         --  Translate a return statement by raising the predefined exception
         --  for returns, which is caught at the end of the subprogram. For
         --  functions, store the value returned in the local special variable
         --  for returned values, prior to raising the exception.

         when N_Simple_Return_Statement =>
            declare
               Raise_Stmt  : W_Prog_Id :=
                 New_Raise
                   (Ada_Node => Stmt_Or_Decl,
                    Name     => M_Main.Return_Exc,
                    Typ      => EW_Unit_Type);
               Result_Stmt : W_Prog_Id;

            begin
               --  Havoc objects borrowed in scopes traversed by the return
               --  statement.

               Raise_Stmt :=
                 Sequence (Havoc_Borrowed_On_Return, Raise_Stmt);

               if Expression (Stmt_Or_Decl) /= Empty then
                  declare
                     Subp        : constant Entity_Id := Return_Applies_To
                       (Return_Statement_Entity (Stmt_Or_Decl));
                     Return_Type : constant W_Type_Id :=
                       Type_Of_Node (Subp);
                  begin
                     Result_Stmt :=
                       +Transform_Expr (Expression (Stmt_Or_Decl),
                                        Return_Type,
                                        EW_Prog,
                                        Params => Body_Params);

                     Insert_Move_Of_Deep_Parts (Stmt    => Stmt_Or_Decl,
                                                Lhs_Typ => Etype (Subp),
                                                Expr    => Result_Stmt);

                     Result_Stmt :=
                       New_Assignment
                         (Ada_Node => Stmt_Or_Decl,
                          Name     => Result_Name,
                          Labels   => Symbol_Sets.Empty_Set,
                          Value    => +Result_Stmt,
                          Typ      => Type_Of_Node
                            (Return_Applies_To
                               (Return_Statement_Entity (Stmt_Or_Decl))));

                     --  Update the pledge of the result

                     if Is_Borrowing_Traversal_Function (Subp) then
                        --  If the result is null, then the borrowed object
                        --  cannot be modified.

                        if Nkind (Expression (Stmt_Or_Decl)) = N_Null then
                           declare
                              Borrowed    : constant Entity_Id :=
                                First_Formal (Subp);
                              Brower_Id   : constant W_Identifier_Id :=
                                New_Temp_Identifier
                                  (Typ       => Type_Of_Node (Etype (Subp)),
                                   Base_Name => "brower");
                              Borrowed_Id : constant W_Identifier_Id :=
                                New_Temp_Identifier
                                  (Typ       =>
                                      Type_Of_Node (Etype (Borrowed)),
                                   Base_Name => "borrowed");
                           begin
                              Result_Stmt :=
                                Sequence
                                  (Result_Stmt,
                                   New_Pledge_Update
                                     (E           => Subp,
                                      Borrowed_Id => Borrowed_Id,
                                      Brower_Id   => Brower_Id,
                                      Def         => +New_Comparison
                                        (Symbol => Why_Eq,
                                         Left   => +Borrowed_Id,
                                         Right  => Transform_Identifier
                                           (Params   => Body_Params,
                                            Expr     => Borrowed,
                                            Ent      => Borrowed,
                                            Domain   => EW_Term),
                                         Domain => EW_Term)));
                           end;

                        --  Otherwise, compute the pledge from the assignment

                        else
                           Result_Stmt :=
                             Sequence
                               (Result_Stmt,
                                New_Pledge_Update_From_Assignment
                                  (Brower => Subp,
                                   Path   => Expression (Stmt_Or_Decl)));
                        end if;
                     end if;

                     return Sequence (Result_Stmt, Raise_Stmt);
                  end;
               else
                  return Raise_Stmt;
               end if;
            end;

         when N_Extended_Return_Statement =>
            declare
               Raise_Stmt : constant W_Prog_Id :=
                 New_Raise
                   (Ada_Node => Stmt_Or_Decl,
                    Name     => M_Main.Return_Exc);
               Expr       : W_Prog_Id :=
                 Transform_Statements_And_Declarations
                   (Return_Object_Declarations (Stmt_Or_Decl));
               Ret_Obj    : constant Entity_Id :=
                 Get_Return_Object (Stmt_Or_Decl);
               Ret_Type   : constant W_Type_Id :=
                 Type_Of_Node (Current_Subp);
               Obj_Deref  : constant W_Prog_Id :=
                 +Insert_Simple_Conversion
                   (Domain => EW_Prog,
                    Expr   => Transform_Identifier
                      (Params => Body_Params,
                       Expr   => Ret_Obj,
                       Ent    => Ret_Obj,
                       Domain => EW_Prog),
                    To     => Ret_Type);

            begin
               if Present (Handled_Statement_Sequence (Stmt_Or_Decl)) then
                  Expr :=
                    Sequence
                      (Expr,
                       Transform_Statements_And_Declarations
                         (Statements
                            (Handled_Statement_Sequence (Stmt_Or_Decl))));
               end if;

               --  Wrap the sequence of statements inside a try block, in case
               --  it contains a return statement.

               return
                 New_Try_Block
                   (Prog    => Sequence
                      ((1 => Expr,

                        --  Havoc objects borrowed in scopes traversed by the
                        --  return statement.

                        2 => Havoc_Borrowed_On_Return,

                        --  Raise statement

                        3 => Raise_Stmt)),

                    Handler =>
                      (1 => New_Handler
                         (Name => M_Main.Return_Exc,
                          Def  => Sequence

                            --  Assign the result name

                            (New_Assignment
                                 (Name     => Result_Name,
                                  Value    => Obj_Deref,
                                  Labels   => Symbol_Sets.Empty_Set,
                                  Typ      => Ret_Type),

                             --  Reraise the exception

                             Raise_Stmt))));
            end;

         when N_Goto_Statement =>
            declare
               Raise_Stmt : constant W_Prog_Id :=
                 New_Raise
                   (Ada_Node => Stmt_Or_Decl,
                    Name     => Goto_Exception_Name
                      (Entity (Name (Stmt_Or_Decl))),
                    Typ      => EW_Unit_Type);

            begin
               --  Havoc objects borrowed in scopes traversed by the goto
               --  statement.

               return Sequence
                 (Havoc_Borrowed_On_Goto, Raise_Stmt);
            end;

         when N_Procedure_Call_Statement
            | N_Entry_Call_Statement
         =>
            declare
               Context  : Ref_Context;
               Store    : constant W_Statement_Sequence_Unchecked_Id :=
                 New_Unchecked_Statement_Sequence;
               Call     : W_Expr_Id;
               Subp     : constant Entity_Id :=
                 Get_Called_Entity (Stmt_Or_Decl);

               Args     : constant W_Expr_Array :=
                 Compute_Call_Args
                   (Stmt_Or_Decl, EW_Prog, Context, Store,
                    Params => Body_Params);

               Selector : constant Selection_Kind :=
                  --  When calling an error-signaling procedure from an
                  --  ordinary program unit, use the No_Return variant of the
                  --  program function, which has a precondition of False. This
                  --  ensures that a check is issued for each such call, to
                  --  detect when they are reachable.

                 (if Is_Error_Signaling_Statement (Stmt_Or_Decl) then
                     No_Return

                  --  When the call is dispatching, use the Dispatch variant of
                  --  the program function, which has the appropriate contract.

                  elsif Nkind (Stmt_Or_Decl) = N_Procedure_Call_Statement
                    and then Present (Controlling_Argument (Stmt_Or_Decl))
                  then
                     Dispatch

                  --  When the call has visibility over the refined
                  --  postcondition of the subprogram, use the Refine variant
                  --  of the program function, which has the appropriate
                  --  refined contract.

                  elsif Entity_Body_In_SPARK (Subp)
                    and then Has_Contracts (Subp, Pragma_Refined_Post)
                    and then Has_Visibility_On_Refined (Stmt_Or_Decl, Subp)
                  then
                     Refine

                  --  Otherwise use the Standard variant of the program
                  --  function (defined outside any namespace, directly in
                  --  the module for the program function).

                  else Why.Inter.Standard);

               Why_Name : constant W_Identifier_Id :=
                 W_Identifier_Id
                   (Transform_Identifier (Params   => Body_Params,
                                          Expr     => Stmt_Or_Decl,
                                          Ent      => Subp,
                                          Domain   => EW_Prog,
                                          Selector => Selector));
            begin
               if Why_Subp_Has_Precondition (Subp, Selector) then
                  Call :=
                    +New_VC_Call
                      (Stmt_Or_Decl,
                       Why_Name,
                       Args,
                       VC_Precondition,
                       EW_Prog,
                       EW_Unit_Type);
               else
                  Call :=
                    New_Call
                      (Stmt_Or_Decl,
                       EW_Prog,
                       Why_Name,
                       Args,
                       EW_Unit_Type);
               end if;

               --  If a procedure might not return, ignore the case where it
               --  does not return after the call:
               --
               --    proc;
               --    assume (no__return = False);

               if Has_Might_Not_Return_Annotation (Subp) then
                  Call := +Sequence
                    (+Call,
                     New_Assume_Statement
                       (Ada_Node => Stmt_Or_Decl,
                        Pred     =>
                          +New_Comparison
                            (Symbol => M_Integer.Bool_Eq,
                             Left   => New_Deref (Right => +M_Main.No_Return,
                                                  Typ   => EW_Bool_Type),
                             Right  => +False_Term,
                             Domain => EW_Term)));
               end if;

               --  Insert invariant check if needed

               if Subp_Needs_Invariant_Checks (Subp) then
                  Call := +Sequence
                    (+New_VC_Call
                       (Ada_Node => Stmt_Or_Decl,
                        Name     =>
                          E_Symb (Subp, WNE_Check_Invariants_On_Call),
                        Progs    => Args,
                        Reason   => VC_Invariant_Check,
                        Domain   => EW_Prog,
                        Typ      => EW_Unit_Type),
                     +Call);
               end if;

               --  Insert tag check if needed

               Call :=
                 +Sequence (Compute_Tag_Check (Stmt_Or_Decl, Body_Params),
                            +Call);

               --  Check that the call does not cause a memory leak. Every
               --  output of the call which is not also an input should be
               --  moved prior to the call. Otherwise assigning it in the
               --  callee will produce a memory leak.

               Check_For_Memory_Leak : declare

                  Outputs : Entity_Sets.Set :=
                    Compute_Deep_Outputs (Subp);

                  procedure Check_Param
                    (Formal : Entity_Id; Actual : Node_Id);

                  procedure Check_Param
                    (Formal : Entity_Id; Actual : Node_Id)
                  is
                     Typ : constant Entity_Id := Retysp (Etype (Formal));
                  begin
                     if Is_Deep (Typ)
                       and then not Is_Anonymous_Access_Type (Typ)
                       and then Ekind (Formal) = E_Out_Parameter
                     then
                        Outputs.Delete (Formal);
                        Call := +Sequence
                          (Check_No_Memory_Leaks (Actual, Actual), +Call);
                     end if;
                  end Check_Param;

                  procedure Iterate_Call is new
                    Iterate_Call_Parameters (Check_Param);

               begin
                  if Is_Unchecked_Deallocation_Instance (Subp) then
                     Call := +Sequence
                       (Check_No_Memory_Leaks
                          (Stmt_Or_Decl,
                           First_Actual (Stmt_Or_Decl),
                           Is_Uncheck_Dealloc => True), +Call);

                  else
                     Iterate_Call (Stmt_Or_Decl);

                     for Obj of Outputs loop
                        Call := +Sequence
                          (Check_No_Memory_Leaks (Stmt_Or_Decl, Obj), +Call);
                     end loop;
                  end if;
               end Check_For_Memory_Leak;

               --  Always call Insert_Ref_Context to get the checks on store
               --  for predicates.

               Call :=
                 +Insert_Ref_Context (Stmt_Or_Decl, +Call, Context, Store);

               --  Handle specially calls to instances of
               --  Ada.Unchecked_Deallocation to assume that the argument is
               --  set to null on return, in the absence of a postcondition
               --  in the standard.

               if Is_Unchecked_Deallocation_Instance (Subp) then
                  declare
                     Actual : constant Node_Id := First_Actual (Stmt_Or_Decl);
                     Typ    : constant Entity_Id := Retysp (Etype (Actual));
                     Ptr    : constant W_Expr_Id :=
                       Transform_Expr (Expr   => Actual,
                                       Domain => EW_Term,
                                       Params => Body_Params);
                  begin
                     Call := +Sequence (+Call,
                       New_Assume_Statement
                         (Ada_Node => Stmt_Or_Decl,
                          Pred     =>
                            Pred_Of_Boolean_Term
                              (+New_Pointer_Is_Null_Access (Typ, Ptr))));
                  end;
               end if;

               return +Call;
            end;

         when N_If_Statement =>
            declare
               Then_Part : constant List_Id := Then_Statements (Stmt_Or_Decl);
               Then_Stmt : W_Prog_Id :=
                 Transform_Statements_And_Declarations (Then_Part);
               Else_Part : constant List_Id := Else_Statements (Stmt_Or_Decl);
               Else_Stmt : W_Prog_Id :=
                 Transform_Statements_And_Declarations (Else_Part);

               Do_Warn_On_Dead_Branch : Boolean := True;
               --  Whether we should warn on dead branches. This may be set
               --  to False is we encounter a test for X'Valid.

            begin
               --  Possibly warn on dead code

               Warn_On_Dead_Branch_Condition_Update (Condition (Stmt_Or_Decl),
                                                     Do_Warn_On_Dead_Branch);
               if Do_Warn_On_Dead_Branch then
                  Then_Stmt :=
                    +Warn_On_Dead_Code (First (Then_Part),
                                        +Then_Stmt,
                                        Generate_VCs_For_Body);

                  if List_Length (Else_Part) > 0 then
                     Else_Stmt :=
                       +Warn_On_Dead_Code (First (Else_Part),
                                           +Else_Stmt,
                                           Generate_VCs_For_Body);
                  end if;
               end if;

               if Present (Elsif_Parts (Stmt_Or_Decl)) then
                  declare
                     Cur      : Node_Id := Last (Elsif_Parts (Stmt_Or_Decl));
                     Cur_Stmt : W_Prog_Id;
                  begin
                     --  Beginning from the tail that consists of the
                     --  translation of the Else part, possibly a no-op,
                     --  translate the list of elsif parts into a chain of
                     --  if-then-else Why expressions.

                     while Present (Cur) loop
                        Cur_Stmt :=
                          Transform_Statements_And_Declarations
                            (Then_Statements (Cur));

                        --  Possibly warn on an unreachable case branch

                        Warn_On_Dead_Branch_Condition_Update
                          (Condition (Cur),
                           Do_Warn_On_Dead_Branch);
                        if Do_Warn_On_Dead_Branch then
                           Cur_Stmt :=
                             +Warn_On_Dead_Code
                               (First (Then_Statements (Cur)),
                                +Cur_Stmt,
                                Generate_VCs_For_Body);
                        end if;

                        Else_Stmt :=
                          New_Label
                            (Labels =>
                               Symbol_Sets.To_Set (New_Located_Label (Cur)),
                             Def    =>
                             +New_Simpl_Conditional
                               (Condition =>
                                  New_Counterexample_Assign (Cur,
                                  Transform_Expr_With_Actions
                                    (Condition (Cur),
                                     Condition_Actions (Cur),
                                     EW_Bool_Type,
                                     EW_Prog,
                                     Params => Body_Params)),
                                Then_Part => +Cur_Stmt,
                                Else_Part => +Else_Stmt,
                                Domain    => EW_Prog),
                                Typ       => EW_Unit_Type);
                        Prev (Cur);
                     end loop;
                  end;
               end if;

               --  Finish by putting the main if-then-else on top.

               return
                 +New_Simpl_Conditional
                 (Condition =>
                    New_Counterexample_Assign (Stmt_Or_Decl,
                    Transform_Expr (Condition (Stmt_Or_Decl),
                                               EW_Bool_Type,
                                               EW_Prog,
                                               Params => Body_Params)),
                    Then_Part => +Then_Stmt,
                    Else_Part => +Else_Stmt,
                    Domain    => EW_Prog);
            end;

         when N_Object_Declaration
            | N_Subtype_Declaration
            | N_Full_Type_Declaration
         =>
            return Transform_Declaration (Stmt_Or_Decl);

         when N_Loop_Statement =>
            return Transform_Loop_Statement (Stmt_Or_Decl);

         when N_Exit_Statement =>
            return Transform_Exit_Statement (Stmt_Or_Decl);

         when N_Case_Statement =>
            return
              +Case_Expr_Of_Ada_Node
                 (N           => Stmt_Or_Decl,
                  Domain      => EW_Prog,
                  Params      => Body_Params);

         when N_Block_Statement =>
            return Transform_Block_Statement (Stmt_Or_Decl);

         when N_Pragma =>
            if Is_Pragma_Assert_And_Cut (Stmt_Or_Decl) then
               declare
                  Expr       : Node_Id;
                  Check_Expr : W_Prog_Id;
                  Pred       : W_Pred_Id;
               begin
                  Transform_Pragma_Check (Stmt_Or_Decl,
                                          Force   => False,
                                          Expr    => Expr,
                                          Runtime => Check_Expr,
                                          Pred    => Pred);
                  Assert_And_Cut_Expr := Expr;
                  Assert_And_Cut := Pred;
               end;
            end if;

            return Transform_Pragma (Stmt_Or_Decl, Force => False);

         when N_Raise_xxx_Error
            | N_Raise_Statement
         =>
            return Transform_Raise (Stmt_Or_Decl);

         --  Subprogram and package declarations are already taken care of
         --  explicitly. They should not be treated as part of a list of
         --  declarations.

         when N_Package_Body
            | N_Package_Declaration
            | N_Subprogram_Body
            | N_Subprogram_Declaration
         =>
            return +Void;

         when N_Delay_Statement =>
            return
              New_Ignore (Ada_Node => Stmt_Or_Decl,
                          Prog     =>
                             +Transform_Expr
                            (Expression (Stmt_Or_Decl),
                             Domain => EW_Prog,
                             Params => Body_Params));

         when others =>
            Ada.Text_IO.Put_Line ("[Transform_Statement] kind ="
                                  & Node_Kind'Image (Nkind (Stmt_Or_Decl)));
            raise Not_Implemented;
      end case;
   end Transform_Statement_Or_Declaration;

   ------------------------------------------------
   -- Transform_Statement_Or_Declaration_In_List --
   ------------------------------------------------

   procedure Transform_Statement_Or_Declaration_In_List
     (Stmt_Or_Decl : Node_Id;
      Seq          : in out W_Statement_Sequence_Id)
   is
      Cut_Assertion_Expr : Node_Id;
      Cut_Assertion      : W_Pred_Id;
      Prog               : constant W_Prog_Id :=
        +Insert_Cnt_Loc_Label
        (Stmt_Or_Decl,
         +Transform_Statement_Or_Declaration
           (Stmt_Or_Decl        => Stmt_Or_Decl,
            Assert_And_Cut_Expr => Cut_Assertion_Expr,
            Assert_And_Cut      => Cut_Assertion));
   begin
      Sequence_Append (Seq,
                       New_Label (Labels => Symbol_Sets.To_Set
                                  (New_Located_Label (Stmt_Or_Decl)),
                                  Def    => +Prog));

      --  If we are translating a label, catch the exception which may have
      --  been raised by goto statements referencing this label.

      if Nkind (Stmt_Or_Decl) = N_Label then
         pragma Assert (Cut_Assertion = Why_Empty);

         declare
            Exc : constant W_Name_Id := Goto_Exception_Name
              (Entity (Identifier (Stmt_Or_Decl)));
         begin
            Insert_Exception (Exc);
            Seq :=
              +Sequence
              (Progs =>
                 (1 => New_Try_Block
                      (Ada_Node => Stmt_Or_Decl,
                       Prog     => +Seq,
                       Handler  =>
                         (1 => New_Handler
                            (Ada_Node => Stmt_Or_Decl,
                             Name     => Exc,
                             Def      => +Void)))));
         end;

      --  If we are translating an Assert_And_Cut pragma, enclose the previous
      --  statements in an abstract block and only keep the Cut_Assertion.

      elsif Cut_Assertion /= Why_Empty then
         Seq :=
           +Sequence
             (Progs =>
                (1 => New_Located_Abstract
                   (Ada_Node => Cut_Assertion_Expr,
                    Expr     => +Seq,
                    Post     => Cut_Assertion,
                    Reason   => VC_Assert)));

         --  Assume the dynamic property of variables referenced in
         --  Cut_Assertion.
         --  ??? We should add the dynamic property of variables modified
         --  in the previous statements, but it is more difficult to get.

         declare
            Vars : constant Node_Sets.Set :=
              Compute_Ada_Node_Set (+Cut_Assertion);
         begin
            for V of Vars loop
               if Nkind (V) in N_Entity
                 and then Is_Object (V)
                 and then Ada_Ent_To_Why.Has_Element (Symbol_Table, V)
                 and then Is_Mutable_In_Why (V)
               then
                  Sequence_Append (Seq,
                                   Assume_Dynamic_Invariant
                                     (Expr          => +Transform_Identifier
                                        (Params   => Body_Params,
                                         Expr     => V,
                                         Ent      => V,
                                         Domain   => EW_Term),
                                      Ty            => Etype (V),
                                      Initialized   => False,
                                      Only_Var      => True,
                                      Top_Predicate => True));
               end if;
            end loop;
         end;
      end if;

   end Transform_Statement_Or_Declaration_In_List;

   -------------------------------------------
   -- Transform_Statements_And_Declarations --
   -------------------------------------------

   function Transform_Statements_And_Declarations
     (Stmts_And_Decls : List_Id) return W_Prog_Id
   is
      Cur_Stmt_Or_Decl : Node_Id   := Nlists.First (Stmts_And_Decls);
      Result           : W_Statement_Sequence_Id := Void_Sequence;

   begin
      if No (Cur_Stmt_Or_Decl) then
         return +Void;
      end if;

      while Present (Cur_Stmt_Or_Decl) loop
         Transform_Statement_Or_Declaration_In_List
           (Stmt_Or_Decl => Cur_Stmt_Or_Decl,
            Seq          => Result);

         Nlists.Next (Cur_Stmt_Or_Decl);
      end loop;

      --  If inside a loop, with the last instruction being an unconditional
      --  exit or return statement, and provided the loop is not unrolled,
      --  we store the Why3 expression in a map, and return instead the raise
      --  expression that will be linked to that treatment.

      declare
         Expr : W_Prog_Id := +Result;
      begin
         Loops.Exits.Record_And_Replace (Stmts_And_Decls, Expr);
         return Expr;
      end;
   end Transform_Statements_And_Declarations;

   ------------------------------
   -- Transform_String_Literal --
   ------------------------------

   procedure Transform_String_Literal
     (Params : Transformation_Params;
      N      : Node_Id)
   is
      Name      : constant String := New_Temp_Identifier ("String_Literal");
      Ty        : constant Entity_Id := Type_Of_Node (N);
      Why_Type  : constant W_Type_Id := New_Abstract_Base_Type (Ty);
      Id        : constant W_Identifier_Id :=
        New_Identifier (Ada_Node => N,
                        Name     => Name,
                        Typ      => Why_Type);
      Binders   : constant Binder_Array := (1 .. 1 => Unit_Param);
      Decl_File : constant W_Section_Id := Dispatch_Entity (N);
      Save_Theory : W_Theory_Declaration_Id;
   begin
      if Params.File = Decl_File then
         Save_Theory := Why_Sections (Decl_File).Cur_Theory;
         Why_Sections (Decl_File).Cur_Theory := Why_Empty;
      end if;

      Insert_Extra_Module
        (N,
         New_Module (File => No_Symbol, Name => Name));

      Open_Theory (Decl_File, E_Module (N),
                   Comment =>
                     "Module for defining a value for string literal "
                       & (if Sloc (N) > 0 then
                            " defined at " & Build_Location_String (Sloc (N))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Generate an abstract logic function for the Why3 map of the literal.
      --  Use a function with a unit parameter instead of a constant so that
      --  the axiom is only instanciated when the literal is used.

      Emit
        (Decl_File,
         New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => Id,
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Binders     => Binders,
            Return_Type => Why_Type));

      --  We now generate an axiom which gives the values stored in Id

      declare
         Call         : constant W_Term_Id :=
           +New_Call (Domain  => EW_Term,
                      Name    => Id,
                      Binders => Binders,
                      Typ     => Why_Type);
         Axiom_Name   : constant String := Name & "__" & Def_Axiom;
         Str_Value    : constant String_Id := Strval (N);
         Len          : constant Nat := String_Length (Str_Value);
         Low_Bound    : constant Int :=
           UI_To_Int (Expr_Value (String_Literal_Low_Bound (Ty)));
         Value_String : String (1 .. Natural (Len));
         B_Ty         : constant W_Type_Id :=
           Nth_Index_Rep_Type_No_Bool (Ty, 1);
         Def          : W_Pred_Id := True_Pred;

      begin
         --  Fetch the value of the string literal

         String_To_Name_Buffer (Str_Value);
         Value_String := Name_Buffer (1 .. Natural (Len));

         --  For each index in the string, add an assumption specifying the
         --  value stored in Id at this index.

         if Len > 0 then
            declare
               Expr_Ar : W_Expr_Array (1 .. Positive (Len));
            begin
               for I in 1 .. Len loop
                  declare
                     Arr_Val : constant W_Expr_Id :=
                       New_Array_Access
                         (Ada_Node => Empty,
                          Ar       => +Call,
                          Index    =>
                            (1 => New_Discrete_Constant
                               (Value => UI_From_Int (I - 1 + Low_Bound),
                                Typ   => B_Ty)),
                          Domain   => EW_Term);
                     Char   : constant W_Expr_Id :=
                       New_Integer_Constant
                         (Value => UI_From_CC
                            (Get_Char_Code (Value_String (Positive (I)))));
                  begin
                     Expr_Ar (Positive (I)) :=
                       New_Comparison
                         (Symbol => Why_Eq,
                          Left   => Insert_Simple_Conversion
                            (Domain => EW_Term,
                             Expr   => Arr_Val,
                             To     => EW_Int_Type),
                          Right  => Char,
                          Domain => EW_Pred);
                  end;
               end loop;
               Def := +New_And_Expr (Expr_Ar, EW_Pred);
            end;
         end if;

         --  Emit an axiom containing all the assumptions

         Emit
           (Decl_File,
            New_Axiom
              (Ada_Node => N,
               Name     => NID (Axiom_Name),
               Def      => New_Universal_Quantif
                 (Binders  => Binders,
                  Triggers => New_Triggers
                    (Triggers => (1 => New_Trigger (Terms => (1 => +Call)))),
                  Pred     => Def)));
      end;

      Close_Theory (Decl_File,
                    Kind => Definition_Theory,
                    Defined_Entity => N);

      if Params.File = Decl_File then
         Why_Sections (Decl_File).Cur_Theory := Save_Theory;
      end if;
   end Transform_String_Literal;

   -------------------------------
   -- Type_Invariant_Expression --
   -------------------------------

   function Type_Invariant_Expression
     (Expr     : W_Expr_Id;
      Inv_Subp : Entity_Id;
      Domain   : EW_Domain;
      Params   : Transformation_Params) return W_Expr_Id
   is
      Result    : W_Expr_Id;
      Inv_Expr  : constant Node_Id :=
        Get_Expr_From_Check_Only_Proc (Inv_Subp);
      Inv_Param : constant Entity_Id := First_Formal (Inv_Subp);
      Inv_Id    : constant W_Identifier_Id :=
        New_Temp_Identifier (Inv_Param, Get_Type (+Expr));

   begin
      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      --  Register the temporary identifier Inv_Id for parameter Inv_Param in
      --  the symbol table. This ensures both that a distinct name is used each
      --  time (preventing name capture), and that the type of Expr is used as
      --  the type used to represent Inv_Param (avoiding type conversion).

      if Get_Type_Kind (Get_Type (+Expr)) = EW_Split
        and then Has_Array_Type (Get_Ada_Node (+Get_Type (+Expr)))
      then
         declare
            E : constant Item_Type :=
              Ada_Ent_To_Why.Element
                (Symbol_Table, Get_Entity_Of_Variable (+Expr));
         begin
            Insert_Item
              (I => Item_Type'(Kind    => UCArray,
                               Local   => E.Local,
                               Init    => <>,
                               Content =>
                                 Binder_Type'(B_Name => Inv_Id,
                                              others => <>),
                               Dim     => E.Dim,
                               Bounds  => E.Bounds),
               E => Inv_Param);
         end;
      else
         Insert_Entity (Inv_Param, Inv_Id);
      end if;

      --  Transform the invariant expression into Why3

      Result := +Transform_Expr (Expr   => Inv_Expr,
                                 Domain => Domain,
                                 Params => Params);

      --  Relate the name Inv_Id used in the invariant expression to the
      --  value Expr for which the invariant is checked.

      Result := New_Binding (Name    => Inv_Id,
                             Def     => +Expr,
                             Context => +Result,
                             Domain  => Domain,
                             Typ     => Get_Type (+Result));

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      return Result;
   end Type_Invariant_Expression;

   -------------------------------
   -- Variables_In_Default_Init --
   -------------------------------

   procedure Variables_In_Default_Init
     (Ty        : Entity_Id;
      Variables : in out Flow_Id_Sets.Set)
   is
      Ty_Ext : constant Entity_Id := Retysp (Ty);
   begin
      if Is_Scalar_Type (Ty_Ext) then
         if Has_Default_Aspect (Ty_Ext) then
            Variables.Union (Get_Variables_For_Proof
                             (Default_Aspect_Value (Ty_Ext), Ty_Ext));
         end if;
      elsif Is_Array_Type (Ty_Ext)
        and then Ekind (Ty_Ext) /= E_String_Literal_Subtype
      then
         pragma Assert (Is_Constrained (Ty_Ext));

         --  Generates:
         --  forall i1 : int ..
         --   in_range (i1) /\ .. ->
         --    get (<Expr>, i1, ...) = <Default_Component_Value>    <if any>
         --    default_init (get (<Expr>, i1, ...), Component_Type) <otherwise>

         if Has_Default_Aspect (Ty_Ext) then

            --  if Ty_Ext as a Default_Component_Value aspect,
            --  generate get (<Expr>, i1, ...) = <Default_Component_Value>

            Variables.Union (Get_Variables_For_Proof
                               (Default_Aspect_Component_Value (Ty_Ext),
                                Ty_Ext));
         else

            --  otherwise, use its Component_Type default value.

            Variables_In_Default_Init (Component_Type (Ty_Ext), Variables);
         end if;

         --  Add variables for bounds of dynamically constrained types

         if Is_Constrained (Ty_Ext)
           and then not Is_Static_Array_Type (Ty_Ext)
         then
            declare
               Index : Node_Id := First_Index (Ty_Ext);
            begin
               while Present (Index) loop
                  Variables.Union (Get_Variables_For_Proof
                                   (Low_Bound (Get_Range (Index)), Ty_Ext));
                  Variables.Union (Get_Variables_For_Proof
                                   (High_Bound (Get_Range (Index)), Ty_Ext));
                  Next_Index (Index);
               end loop;
            end;
         end if;

      elsif Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then

         --  Generates:
         --  let tmp1 = <Expr>.rec__disc1 in
         --  <Expr>.is_constrained = False /\ <if Ty_Ext as default discrs>
         --  <Expr>.rec__disc1 = Discr1.default  <if Ty_Ext is unconstrained>
         --  <Expr>.rec__disc1 = Discr1 /\ ..    <if Ty_Ext is constrained>
         --  (check_for_field1 expr ->
         --      <Expr>.rec__field1 = Field1.def      <if Field1 has a default>
         --      default_init (<Expr>.rec__field1, Etype (Field1))) <otherwise>
         --  /\ ..

         declare
            Num_Discr : constant Natural := Count_Discriminants (Ty_Ext);

            Discr  : Node_Id := (if Num_Discr > 0
                                 then First_Discriminant (Ty_Ext)
                                 else Empty);
            Elmt   : Elmt_Id :=
              (if Num_Discr > 0
               and then Is_Constrained (Ty_Ext)
               then First_Elmt (Stored_Constraint (Ty_Ext))
               else No_Elmt);
         begin

            --  Go through discriminants to create
            --  <Expr>.rec__disc1 = Discr1.default <if Ty_Ext is unconstrained>
            --  <Expr>.rec__disc1 = Discr1 /\ ..   <if Ty_Ext is constrained>

            while Present (Discr) loop
               if Is_Constrained (Ty_Ext) then

                  --  Generate <Expr>.rec__disc1 = Discr

                  Variables.Union
                    (Get_Variables_For_Proof (Node (Elmt), Ty_Ext));
                  Next_Elmt (Elmt);
               else
                  pragma Assert (Has_Defaulted_Discriminants (Ty_Ext));

                  --  Generate <Expr>.rec__disc1 = Discr1.default

                  Variables.Union (Get_Variables_For_Proof
                                   (Discriminant_Default_Value (Discr),
                                      Ty_Ext));
               end if;
               Next_Discriminant (Discr);
            end loop;

            --  Go through other fields to create the expression
            --  (check_for_field1 expr ->
            --   <Expr>.rec__field1 = Field1.def      <if Field1 has a default>
            --   default_init (<Expr>.rec__field1, Etype (Field1))) <otherwise>
            --  /\ ..

            if Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then

               for Field of Get_Component_Set (Ty_Ext) loop
                  if not Is_Type (Field) then
                     if Present (Expression (Enclosing_Declaration (Field)))
                     then

                        --  if Field has a default expression, use it.
                        --   <Expr>.rec__field1 = Field1.default

                        Variables.Union
                          (Get_Variables_For_Proof
                             (Expression (Enclosing_Declaration (Field)),
                              Ty_Ext));
                     else

                        --  otherwise, use its Field's Etype default value.
                        --   default_init (<Expr>.rec__field1, Etype (Field1)))

                        Variables_In_Default_Init (Etype (Field), Variables);
                     end if;
                  end if;
               end loop;
            end if;
         end;
      end if;

      --  Assume the default initial condition for Ty, when specified as a
      --  boolean expression.

      if Has_DIC (Ty) then
         declare
            Default_Init_Subp : constant Entity_Id :=
              Get_Initial_DIC_Procedure (Ty);
         begin
            if Present (Default_Init_Subp) then
               declare
                  Default_Init_Expr : constant Node_Id :=
                    Get_Expr_From_Check_Only_Proc (Default_Init_Subp);
                  Init_Param : constant Entity_Id :=
                    First_Formal (Default_Init_Subp);
               begin
                  if Present (Default_Init_Expr) then

                     Variables.Union (Get_Variables_For_Proof
                                      (Default_Init_Expr, Ty_Ext));

                     --  Remove parameter of DIC procedure

                     Variables.Exclude
                       (Direct_Mapping_Id (Unique_Entity (Init_Param)));
                  end if;
               end;
            end if;
         end;
      end if;
   end Variables_In_Default_Init;

   ------------------------------------
   -- Variables_In_Dynamic_Predicate --
   ------------------------------------

   procedure Variables_In_Dynamic_Predicate
     (Ty        : Entity_Id;
      Variables : in out Flow_Id_Sets.Set)
   is
      Rep_Type : Entity_Id := Retysp (Ty);
   begin
      while Has_Predicates (Rep_Type) loop

         declare
            Pred_Typ : constant Entity_Id :=
              Get_Type_With_Predicate_Function (Rep_Type);
            --  Type entity with predicate function attached
            Pred_Fun : constant Entity_Id := Predicate_Function (Pred_Typ);
         begin
            if Entity_In_SPARK (Pred_Fun) then
               Variables.Union
                 (Get_Variables_For_Proof
                    (Get_Expr_From_Return_Only_Func (Pred_Fun), Pred_Typ));
            end if;

            Rep_Type := Retysp
              (Etype (First_Formal (Predicate_Function (Pred_Typ))));
         end;

         declare
            Next_Ty : constant Entity_Id := Retysp (Etype (Rep_Type));
         begin
            exit when Next_Ty = Rep_Type;
            Rep_Type := Next_Ty;
         end;
      end loop;
   end Variables_In_Dynamic_Predicate;

   ------------------------------------
   -- Variables_In_Dynamic_Invariant --
   ------------------------------------

   procedure Variables_In_Dynamic_Invariant
     (Ty        : Entity_Id;
      Variables : in out Flow_Id_Sets.Set)
   is

      procedure Variables_In_Dynamic_Invariant
        (Ty          : Entity_Id;
         Variables   : in out Flow_Id_Sets.Set;
         Incompl_Acc : in out Entity_Sets.Set);
      --  Auxiliary function with an additional parameter storing access
      --  types to incomplete types already encountered (to avoid looping
      --  on recursive data-structures).

      ------------------------------------
      -- Variables_In_Dynamic_Invariant --
      ------------------------------------

      procedure Variables_In_Dynamic_Invariant
        (Ty          : Entity_Id;
         Variables   : in out Flow_Id_Sets.Set;
         Incompl_Acc : in out Entity_Sets.Set)
      is
         Spec_Ty : constant Entity_Id :=
           (if Is_Class_Wide_Type (Ty)
            then Get_Specific_Type_From_Classwide (Ty)
            else Ty);
         Ty_Ext  : constant Entity_Id := Retysp (Spec_Ty);

      begin
         --  Dynamic property of the type itself

         if Type_Is_Modeled_As_Base (Ty_Ext) then

            --  If a scalar type is not modeled as base, then its bounds are
            --  constants.
            --  Otherwise, variables may occur in their expressions.

            declare
               Rng : constant Node_Id := Get_Range (Ty_Ext);
            begin
               Variables.Union (Get_Variables_For_Proof (Low_Bound (Rng),
                                Ty_Ext));
               Variables.Union (Get_Variables_For_Proof (High_Bound (Rng),
                                Ty_Ext));
            end;
         elsif Is_Array_Type (Ty_Ext)
           and then not Is_Static_Array_Type (Ty_Ext)
         then

            --  Variables coming from the bounds of the index types

            declare
               Index : Node_Id := First_Index (Ty_Ext);
            begin
               while Present (Index) loop
                  if Type_Is_Modeled_As_Base (Etype (Index)) then
                     declare
                        Rng : constant Node_Id := Get_Range (Etype (Index));
                     begin
                        Variables.Union (Get_Variables_For_Proof
                                         (Low_Bound (Rng), Ty_Ext));
                        Variables.Union (Get_Variables_For_Proof
                                         (High_Bound (Rng), Ty_Ext));
                     end;
                  end if;
                  Next_Index (Index);
               end loop;
            end;

            --  If the array is constrained, also assume the value of its
            --  bounds.

            if Is_Constrained (Ty_Ext) then
               declare
                  Index : Node_Id := First_Index (Ty_Ext);
               begin
                  while Present (Index) loop
                     declare
                        Rng : constant Node_Id := Get_Range (Index);
                     begin
                        Variables.Union
                          (Get_Variables_For_Proof (Low_Bound (Rng), Ty_Ext));
                        Variables.Union
                          (Get_Variables_For_Proof (High_Bound (Rng), Ty_Ext));
                     end;
                     Next_Index (Index);
                  end loop;
               end;
            end if;

         elsif Count_Discriminants (Ty_Ext) > 0 then

            --  Variables coming from the record's discriminants

            declare
               Discr : Entity_Id := First_Discriminant (Ty_Ext);
               Elmt  : Elmt_Id :=
                 (if Is_Constrained (Ty_Ext) then
                       First_Elmt (Discriminant_Constraint (Ty_Ext))
                  else No_Elmt);
            begin
               while Present (Discr) loop
                  if Is_Constrained (Ty_Ext) then
                     Variables.Union (Get_Variables_For_Proof (Node (Elmt),
                                      Ty_Ext));
                     Next_Elmt (Elmt);
                  end if;

                  Variables_In_Dynamic_Invariant
                    (Etype (Discr), Variables, Incompl_Acc);
                  Next_Discriminant (Discr);
               end loop;
            end;
         end if;

         --  Variables in the predicate of the type

         if Has_Predicates (Ty_Ext) then
            Variables_In_Dynamic_Predicate (Ty_Ext, Variables);
         end if;

         --  Dynamic Invariant of Ty_Ext's components

         if Is_Array_Type (Ty_Ext)
           and then Ekind (Ty_Ext) /= E_String_Literal_Subtype
         then

            Variables_In_Dynamic_Invariant
              (Component_Type (Ty_Ext), Variables, Incompl_Acc);

         elsif Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then

            for Field of Get_Component_Set (Ty_Ext) loop
               if not Is_Type (Field) then
                  Variables_In_Dynamic_Invariant
                    (Etype (Field), Variables, Incompl_Acc);
               end if;
            end loop;
         elsif Is_Access_Type (Ty_Ext)
           and then
             (not Designates_Incomplete_Type (Repr_Pointer_Type (Ty_Ext))
              or else not Incompl_Acc.Contains (Repr_Pointer_Type (Ty_Ext)))
         then
            if Designates_Incomplete_Type (Repr_Pointer_Type (Ty_Ext)) then
               Incompl_Acc.Insert (Repr_Pointer_Type (Ty_Ext));
            end if;

            Variables_In_Dynamic_Invariant
              (Directly_Designated_Type (Ty_Ext), Variables, Incompl_Acc);
         end if;

         --  External type invariant of Ty_Ext and its parents if any

         declare
            Current : Entity_Id := Ty_Ext;
            Parent  : Entity_Id;
         begin
            loop
               if Has_Invariants_In_SPARK (Current)
                 and then not Has_Visible_Type_Invariants (Current)
               then
                  Variables_In_Type_Invariant (Current, Variables);
               end if;

               Parent := Retysp (Etype (Current));
               exit when Current = Parent;
               Current := Parent;
            end loop;
         end;
      end Variables_In_Dynamic_Invariant;

      --  Local variables

      Incompl_Acc : Entity_Sets.Set;

   --  Start of processing for Variables_In_Dynamic_Invariant

   begin
      Variables_In_Dynamic_Invariant (Ty, Variables, Incompl_Acc);
   end Variables_In_Dynamic_Invariant;

   ---------------------------------
   -- Variables_In_Type_Invariant --
   ---------------------------------

   procedure Variables_In_Type_Invariant
     (Ty        : Entity_Id;
      Variables : in out Flow_Id_Sets.Set)
   is
      Rep_Type      : constant Entity_Id := Retysp (Ty);
      Inv_Subp      : constant Node_Id := Invariant_Procedure (Rep_Type);
      Type_Inv_Expr : constant Node_Id :=
        Get_Expr_From_Check_Only_Proc (Inv_Subp);
      Inv_Param     : constant Entity_Id := First_Formal (Inv_Subp);

   begin
      Variables.Union (Get_Variables_For_Proof (Type_Inv_Expr, Rep_Type));

      --  Remove parameter of invariant procedure

      Variables.Exclude (Direct_Mapping_Id (Unique_Entity (Inv_Param)));
   end Variables_In_Type_Invariant;

   -------------------
   -- Void_Sequence --
   -------------------

   function Void_Sequence return W_Statement_Sequence_Id is
     (New_Statement_Sequence (Ada_Node => Empty,
                              Statements => (1 .. 1 => +Void)));

   -------------------------
   -- Warn_On_Dead_Branch --
   -------------------------

   function Warn_On_Dead_Branch
     (N     : Node_Id;
      W     : W_Expr_Id;
      Phase : Transformation_Phase) return W_Expr_Id
   is
      (Warn_On_Dead_Branch_Or_Code (N, W, Branch => True, Phase => Phase));

   ---------------------------------
   -- Warn_On_Dead_Branch_Or_Code --
   ---------------------------------

   function Warn_On_Dead_Branch_Or_Code
     (N      : Node_Id;
      W      : W_Expr_Id;
      Branch : Boolean;
      Phase  : Transformation_Phase) return W_Expr_Id
   is
      Stmt : W_Prog_Id;

   begin
      --  Only issue a check for unreachable branch if switch --proof-warnings
      --  is set
      if Gnat2Why_Args.Proof_Warnings
        --  and warnings are not suppressed
        and then Opt.Warning_Mode /= Opt.Suppress
        --  and a warning can be issued on that node
        and then May_Issue_Warning_On_Node (N)
        --  and the phase corresponds to generating VCs
        and then Phase in Generate_VCs
        --  and when the next statement if not an unconditional error, signaled
        --  typically as a raise statement or a pragma Assert (False).
        and then not Is_Error_Signaling_Statement (N)
      then
         Stmt :=
           New_Located_Assert
             (Ada_Node => N,
              Pred     => False_Pred,
              Reason   =>
                (if Branch then VC_Unreachable_Branch else VC_Dead_Code),
              Kind     => EW_Check);

         return
           +Sequence
             ((1 => New_Comment (Comment => NID ("Check dead branch "
                                 & Build_Location_String (Sloc (N)))),
               2 => New_Ignore (Prog => Stmt),
               3 => +W));

      --  Otherwise return the argument unmodified

      else
         return W;
      end if;
   end Warn_On_Dead_Branch_Or_Code;

   -----------------------
   -- Warn_On_Dead_Code --
   -----------------------

   function Warn_On_Dead_Code
     (N     : Node_Id;
      W     : W_Prog_Id;
      Phase : Transformation_Phase) return W_Prog_Id
   is
      (+Warn_On_Dead_Branch_Or_Code (N, +W, Branch => False, Phase => Phase));

   ------------------------------------------
   -- Warn_On_Dead_Branch_Condition_Update --
   ------------------------------------------

   procedure Warn_On_Dead_Branch_Condition_Update
     (Cond    : Node_Id;
      Do_Warn : in out Boolean)
   is
   begin
      Do_Warn := Do_Warn

        --  A condition statically True or False means that the branch being
        --  dead is not a useful warning.

        and then not
          (Is_Entity_Name (Cond)
             and then Present (Entity (Cond))
             and then Entity (Cond) in Standard_True | Standard_False)

        --  Similarly for a condition that contains X'Valid

        and then not Expression_Contains_Valid_Or_Valid_Scalars (Cond);
   end Warn_On_Dead_Branch_Condition_Update;

   ---------------------------------
   -- Warn_On_Inconsistent_Assume --
   ---------------------------------

   function Warn_On_Inconsistent_Assume (N : Node_Id) return W_Prog_Id is
      Stmt : W_Prog_Id;

   begin
      --  Only issue a check for unreachable branch if switch --proof-warnings
      --  is set
      if Gnat2Why_Args.Proof_Warnings
        --  and warnings are not suppressed
        and then Opt.Warning_Mode /= Opt.Suppress
        --  and a warning can be issued on that node
        and then May_Issue_Warning_On_Node (N)
      then
         Stmt :=
           New_Located_Assert
             (Ada_Node => N,
              Pred     => False_Pred,
              Reason   => VC_Inconsistent_Assume,
              Kind     => EW_Check);

         return
           Sequence
             ((1 => New_Comment (Comment => NID ("Check inconsistent assume "
                                 & Build_Location_String (Sloc (N)))),
               2 => New_Ignore (Prog => Stmt)));

      else
         return +Void;
      end if;
   end Warn_On_Inconsistent_Assume;

   -------------------------------
   -- Why_Subp_Has_Precondition --
   -------------------------------

   function Why_Subp_Has_Precondition
     (E        : Entity_Id;
      Selector : Selection_Kind := Why.Inter.Standard) return Boolean
   is
      Has_Precondition : constant Boolean :=
        Has_Contracts (E, Pragma_Precondition);
      Has_Classwide_Or_Inherited_Precondition : constant Boolean :=
        Has_Contracts (E, Pragma_Precondition,
                       Classwide => True,
                       Inherited => True);
   begin
      return (Selector /= Dispatch and then Has_Precondition)
        or else Has_Classwide_Or_Inherited_Precondition
        or else Entity_In_Ext_Axioms (E)

        --  E is an error-signaling procedure called outside another
        --  error-signaling procedure (this is what the No_Return variant
        --  means) for which an implicit precondition of False is used.

        or else Selector = No_Return;
   end Why_Subp_Has_Precondition;

end Gnat2Why.Expr;
