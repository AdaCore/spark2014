------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013-2017, Altran UK Limited              --
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
------------------------------------------------------------------------------

--  This package contains a bunch of procedures used throughout flow analysis

with Ada.Containers;
with Atree;                use Atree;
with Common_Containers;    use Common_Containers;
with Einfo;                use Einfo;
with Flow;                 use Flow;
with Flow_Dependency_Maps; use Flow_Dependency_Maps;
with Flow_Types;           use Flow_Types;
with Sem_Util;             use Sem_Util;
with Sinfo;                use Sinfo;
with Snames;               use Snames;
with Stand;                use Stand;
with Types;                use Types;

use type Ada.Containers.Count_Type;

package Flow_Utility
  with Initial_Condition => not Is_Initialized
is

   procedure Initialize with Pre => not Is_Initialized;
   --  Set up state required by some functions in this package

   function Is_Initialized return Boolean with Ghost;
   --  Tests if we're initialized

   procedure Collect_Functions_And_Read_Locked_POs
     (N                  : Node_Id;
      Functions_Called   : out Node_Sets.Set;
      Tasking            : in out Tasking_Info;
      Generating_Globals : Boolean)
   with Pre => Present (N);
   --  For an expression N collect its called functions and update the set of
   --  protected objects that are read-locked when evaluating these functions.
   --
   --  When Generating_Globals is set, then the implicit calls to predicate
   --  functions appear in the set of subprograms called. This is what we
   --  use in phase 1; in phase 2 this should not be set as we add the
   --  global effects directly.

   function Component_Hash (E : Entity_Id) return Ada.Containers.Hash_Type
   with Pre => Is_Initialized and then
                 Nkind (E) = N_Defining_Identifier and then
                 Ekind (E) in E_Component | E_Discriminant;
   --  Compute a suitable hash for the given record component

   procedure Remove_Constants
     (Objects : in out Flow_Id_Sets.Set;
      Skip    :        Node_Sets.Set := Node_Sets.Empty_Set);
   --  Remove from Objects all constants (without variable input) that are not
   --  contained in Skip.
   --  @param Objects are the initial flow ids
   --  @param Skip are the nodes based on which filtering will occur

   procedure Remove_Generic_In_Formals_Without_Variable_Input
     (Objects : in out Flow_Id_Sets.Set);
   --  Remove generic IN formals without variable input from Objects; for SPARK
   --  RM 6.1.4(18):
   --
   --    "If a global_item denotes a generic formal object of mode in, then the
   --     corresponding global_item in an instance of the generic unit may
   --     denote a constant which has no variable inputs. [...] Outside of the
   --     instance, such a global_item is ignored."

   function Same_Component (C1, C2 : Entity_Id) return Boolean
   with Pre => Is_Initialized and then
               Nkind (C1) = N_Defining_Identifier and then
               Nkind (C2) = N_Defining_Identifier and then
               Ekind (C1) in E_Component | E_Discriminant and then
               Ekind (C2) in E_Component | E_Discriminant;
   --  Given two record components, checks if one can be considered to be the
   --  `same' component (for purposes of flow analysis). For example a record
   --  might contain component x, and its derived record also contains this
   --  component x (but it is a different entity). This function can be used
   --  to check for this equivalence.

   function Get_Flow_Id
     (Name : Entity_Name;
      View : Flow_Id_Variant := Normal_Use)
      return Flow_Id;
   --  Return a suitable Flow_Id for the entity name. We try our best to get a
   --  direct mapping, resorting to the magic string only if necessary.
   --  @param Name is the Entity_Name whose corresponding entity we
   --    are looking for
   --  @param View is the view that the returned Flow_Id will have
   --  @return a Flow_Id with either an entity or a magic_string if
   --    an entity cannot be found.

   function To_Flow_Id_Set
     (NS   : Name_Sets.Set;
      View : Flow_Id_Variant := Normal_Use)
      return Flow_Id_Sets.Set;
   --  Converts a name set into a flow id set. The flow ids have their views
   --  set to View.
   --  @param NS is the name set that will be converted
   --  @param View is the view that flow ids will be given
   --  @return the equivalent set of flow ids

   function Has_Depends (Subprogram : Entity_Id) return Boolean
   with Pre => Ekind (Subprogram) in E_Entry     |
                                     E_Function  |
                                     E_Procedure |
                                     E_Task_Type;
   --  Return true if the given subprogram has been annotated with a dependency
   --  relation.

   procedure Get_Depends
     (Subprogram           : Entity_Id;
      Scope                : Flow_Scope;
      Classwide            : Boolean;
      Depends              : out Dependency_Maps.Map;
      Use_Computed_Globals : Boolean := True;
      Callsite             : Node_Id := Empty)
   with Pre  => Ekind (Subprogram) in E_Entry     |
                                      E_Function  |
                                      E_Procedure |
                                      E_Task_Type
                  and then Has_Depends (Subprogram),
        Post => (for all Inputs of Depends =>
                   (for all Input of Inputs => Present (Input)));
   --  Return the dependency relation of the Subprogram, as viewed from the
   --  Scope. Dependency relation is represented as a map from entities to
   --  sets of entities.
   --
   --  For example, (X, Y) =>+ Z is represented as:
   --     x -> {x, z}
   --     y -> {y, z}
   --
   --  This procedure deals with all forms of the Depends annotation. For each
   --  item in the dependency annotation, the LHS and RHS can be any of the
   --  following:
   --     * (x, y, z)     (an aggregate)
   --     * x             (a variable)
   --     * null          (keyword null)
   --  Finally, the dependency annotation can be just a null dependency.
   --
   --  The + shorthand to mean "itself" is expanded away by the front-end and
   --  this procedure does not have to deal with it.
   --
   --  The Use_Computed_Globals flag is set to False during the generation of
   --  globals phase. It prevents us from attempting to use generated globals
   --  before they have actually been produced.

   procedure Get_Globals (Subprogram             : Entity_Id;
                          Scope                  : Flow_Scope;
                          Classwide              : Boolean;
                          Globals                : out Global_Flow_Ids;
                          Consider_Discriminants : Boolean := False;
                          Use_Deduced_Globals    : Boolean := True;
                          Ignore_Depends         : Boolean := False)
   with Pre  => Ekind (Subprogram) in E_Entry     |
                                      E_Function  |
                                      E_Procedure |
                                      E_Task_Type,
        Post => (for all G of Globals.Proof_Ins =>
                   Is_Entire_Variable (G) and then G.Variant = In_View)
       and then (for all G of Globals.Reads =>
                   Is_Entire_Variable (G) and then G.Variant = In_View)
       and then (for all G of Globals.Writes =>
                   Is_Entire_Variable (G) and then G.Variant = Out_View);
   --  Given a subprogram, work out globals from the appropriate global aspect
   --  (relative to Scope), or the depends aspect (if no global aspect is
   --  given). If the Global and Depends aspects are not present then use the
   --  generated globals or finally, if non of the above exist fall back to
   --  the computed globals. The sets returned will contain Flow_Id with the
   --  variant set to In_View and Out_View.
   --
   --  If Consider_Discriminants is True then an out global will include a
   --  corresponding read if the global includes at least one discriminant.
   --
   --  If Use_Deduced_Globals is True, then we will come up with a global
   --  contract ourselves (which is not necessarily correct, but flow will
   --  catch a mismatch between reality and this contract).
   --     - if we have a dependency we work out the globals from that
   --     - if Flow_Generate_Contracts is True (the default) we try:
   --       - globals generated by flow in phase 1 for subprograms in SPARK
   --       - globals generated by the front end for subprograms not in SPARK
   --     - otherwise, we assume "null"
   --
   --  If Ignore_Depends is True then we do not use the Refined_Depends
   --  contract to trim the Globals.

   procedure Get_Proof_Globals (Subprogram          : Entity_Id;
                                Classwide           : Boolean;
                                Reads               : out Flow_Id_Sets.Set;
                                Writes              : out Flow_Id_Sets.Set;
                                Use_Deduced_Globals : Boolean := True;
                                Keep_Constants      : Boolean := False)
   with Pre  => Ekind (Subprogram) in E_Entry     |
                                      E_Function  |
                                      E_Procedure |
                                      E_Task_Type,
        Post => (for all G of Reads =>
                   Is_Entire_Variable (G) and then G.Variant = In_View)
       and then (for all G of Writes =>
                   Is_Entire_Variable (G) and then G.Variant = Out_View);
   --  Same as above but Reads consists of both the Reads and Proof_Ins,
   --  discriminants receive no special handling and globals are proof globals,
   --  and we always return the most refined view possible. If Keep_Constants
   --  is true then constants with variable inputs are not suppressed form the
   --  Globals even if they are constants in Why. For subprograms nested in
   --  protected types, which may have an effect on the components of the
   --  protected type, the protected type itself is returned as a global.

   function Has_Proof_Global_Reads (Subprogram : Entity_Id;
                                    Classwide  : Boolean)
                                    return Boolean
   with Pre => Ekind (Subprogram) in E_Procedure | E_Function;
   --  Returns True if Subprogram has a Global Input or In_Out contract,
   --  whether user-defined or generated.

   function Has_Proof_Global_Writes (Subprogram : Entity_Id;
                                     Classwide  : Boolean)
                                     return Boolean
   with Pre => Ekind (Subprogram) in E_Procedure | E_Function;
   --  Returns True if Subprogram has a Global Output or In_Out contract,
   --  whether user-defined or generated.

   function Rely_On_Generated_Global
     (E     : Entity_Id;
      Scope : Flow_Scope)
      return Boolean
   with Pre => Ekind (E) in E_Entry | E_Function | E_Procedure | E_Task_Type;
   --  Returns True if Scope has visibility of E's body and Generated Globals
   --  will be produced for E.

   function Get_Functions
     (N                  : Node_Id;
      Include_Predicates : Boolean)
      return Node_Sets.Set with
     Pre => Present (N);
   --  Collect functions called in an expression N. If Include_Predicates is
   --  True, then also include implicit calls to predicate functions.

   function Get_Variables
     (N                            : Node_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Assume_In_Expression         : Boolean := True;
      Expand_Synthesized_Constants : Boolean := False;
      Consider_Extensions          : Boolean := False)
      return Flow_Id_Sets.Set
   with Pre  => (if Fold_Functions then Assume_In_Expression),
        Post => (if Reduced
                 then (for all F of Get_Variables'Result
                         => Is_Entire_Variable (F)));
   --  Obtain all variables used in an expression; use Scope to determine if
   --  called subprograms should provide their abstract or refined view.
   --
   --  Local_Constants describes a set of constants (which should all come
   --  from source) which are treated as if they were variables; this means
   --  they are potentially returned by this function.
   --
   --  If Fold_Functions is true, we exclude variables that a function does
   --  not use to derive its result from. For example, given the following
   --  dependency relation on a function:
   --     Depends => (Foo'Result => A,
   --                 null       => B)
   --  Then we return only {A} instead of {A, B} if Fold_Functions is true.
   --
   --  The following other options all have default parameters as they are
   --  only useful in certain usage scenarios. In the majority of flow
   --  analysis one does not have to think about them. They are:
   --
   --     * Reduced: if True, obtain only entire variables.
   --
   --     * Assume_In_Expression: if True, we assume that node N is part of
   --       some kind of expression, and aggressively raise exceptions if we
   --       find nodes that make no sense in such a context.
   --
   --     * Expand_Synthesized_Constants: if True, then constants that do
   --       not come from source are expanded out to the variable set of
   --       their initializing expression.

   function Get_Variables
     (L                            : List_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Assume_In_Expression         : Boolean := True;
      Expand_Synthesized_Constants : Boolean := False)
      return Flow_Id_Sets.Set;
   --  As above, but operating on a list. Note we don't have the
   --  Consider_Extensions parameter here as its implicitly false.

   function Get_Variables_For_Proof (Expr_N  : Node_Id;
                                     Scope_N : Node_Id)
                                     return Flow_Id_Sets.Set
   with Pre  => Present (Expr_N) and then
                Present (Scope_N),
        Post => (for all F of Get_Variables_For_Proof'Result =>
                   Is_Entire_Variable (F));
   --  A wrapper around Get_Variables, as used by proof. Expr_N is the
   --  expression for which we obtain variables, and Scope_N is the node
   --  controlling visibility.

   function Quantified_Variables (N : Node_Id) return Flow_Id_Sets.Set
   with Pre => Present (N);
   --  Return the set of entire variables which are introduced in a quantifier
   --  under node N.

   function Flatten_Variable
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre => F.Kind in Direct_Mapping        |
                         Record_Field          |
                         Magic_String          |
                         Synthetic_Null_Export;
   --  Splits F into parts. For example, we might take X.Y and produce X.Y.A
   --  and X.Y.B, or just X.Y (if we can't see the private part of X.Y's type).
   --
   --  For magic strings and the null export, we simply return a singleton set
   --  with just that.
   --
   --  For null records we return the variable itself.
   --
   --  For private types we just return F. For private types with discriminant
   --  C we return F.C and F'Private_Part.
   --
   --  For tagged types T we just return all components as usual. For classwide
   --  types we also return T'Extension and T'Tag. ??? not true for T'Tag
   --
   --  @param F is the Flow_Id whose parts we need to gather
   --  @param Scope is the scope relative to which we will return the parts
   --  @return all parts of F that are visible from Scope.

   function Flatten_Variable
     (E     : Entity_Id;
      Scope : Flow_Scope)
      return Flow_Id_Sets.Set
   is (Flatten_Variable (Direct_Mapping_Id (Unique_Entity (E)), Scope))
   with Pre => Ekind (E) in E_Abstract_State |
                            E_Function       |
                            Object_Kind      |
                            Type_Kind;
   --  As above, but conveniently taking an Entity_Id instead of a Flow_Id

   function Expand_Abstract_State
     (F               : Flow_Id;
      Erase_Constants : Boolean)
      return Flow_Id_Sets.Set;
   --  If F represents abstract state, return the set of all its components.
   --  Otherwise return F. Additionally, remove formal in parameters from the
   --  set if Erase_Constants is true.

   subtype Valid_Assignment_Kinds is Node_Kind
   with Static_Predicate =>
          Valid_Assignment_Kinds in N_Identifier                |
                                    N_Expanded_Name             |
                                    N_Type_Conversion           |
                                    N_Unchecked_Type_Conversion |
                                    N_Indexed_Component         |
                                    N_Slice                     |
                                    N_Selected_Component;

   function Is_Valid_Assignment_Target (N : Node_Id) return Boolean
   with Post => (if Is_Valid_Assignment_Target'Result
                 then Nkind (N) in Valid_Assignment_Kinds),
        Ghost;
   --  Returns True if the tree under N is a combination of
   --  Valid_Assignment_Kinds only.

   procedure Get_Assignment_Target_Properties
     (N                  : Node_Id;
      Partial_Definition : out Boolean;
      View_Conversion    : out Boolean;
      Classwide          : out Boolean;
      Map_Root           : out Flow_Id;
      Seq                : out Node_Lists.List)
   with Pre  => Is_Valid_Assignment_Target (N),
        Post => Map_Root.Kind in Direct_Mapping | Record_Field and then
                (for all X of Seq => Nkind (X) in Valid_Assignment_Kinds);
   --  Checks the assignment target N and determines a few basic properties
   --
   --  * Partial_Definition: the assignment to N touches only a few elements
   --                        of a larger array.
   --  * View_Conversion: N contains a view conversion.
   --  * Classwide: the assignment to map_root is classwide.
   --  * Map_Root: the non-flattened Flow_Id which is assigned to.
   --  * Seq: items used to derive Map_Root.

   function Original_Constant (N : Node_Id) return Entity_Id
   with Pre  => Nkind (N) in N_Numeric_Or_String_Literal,
        Post => Ekind (Original_Constant'Result) = E_Constant;
   --  For constants that are rewritten to numeric or integer literals return
   --  the original entity. Such rewriting happens for proof, but it obscures
   --  flow contracts, which needs to recover the original constants.

   procedure Untangle_Assignment_Target
     (N                    : Node_Id;
      Scope                : Flow_Scope;
      Local_Constants      : Node_Sets.Set;
      Use_Computed_Globals : Boolean;
      Vars_Defined         : out Flow_Id_Sets.Set;
      Vars_Used            : out Flow_Id_Sets.Set;
      Vars_Proof           : out Flow_Id_Sets.Set;
      Partial_Definition   : out Boolean)
   with Pre  => Is_Valid_Assignment_Target (N),
        Post => (if not Is_Empty_Record_Type (Etype (N))
                 then not Vars_Defined.Is_Empty);
   --  Process the LHS of an assignment statement or an [in] out parameter,
   --  establishing the sets of variables used. For example, assume we have
   --  a function Foo:
   --     function Foo (X : Integer) return Integer
   --     with Global => (Proof_In => Y);
   --  And we process the expression:
   --     A (Foo (B))
   --  Then the variables used will be:
   --     Defined      {A}
   --     Partial      True
   --     Used         {B}
   --     Proof        {Y}
   --  Since we are indexing A and only updating a single element, the
   --  assignment is partial.
   --
   --  The expression denoted by N can be any combination of:
   --     - entire variable
   --     - view conversion (for tagged types)
   --     - array index
   --     - array slice
   --     - record component
   --     - unchecked conversion (for scalars)
   --
   --  Note that the expression(s) in the index or slice can be much more
   --  general and thus will be processed by Get_Variables.
   --
   --  Note we only support unchecked conversion from and to scalars, i.e.
   --  for things generated from:
   --     Foo (Positive (X))

   function Untangle_Record_Assignment
     (N                            : Node_Id;
      Map_Root                     : Flow_Id;
      Map_Type                     : Entity_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Expand_Synthesized_Constants : Boolean;
      Extensions_Irrelevant        : Boolean := True)
      return Flow_Id_Maps.Map
   with Pre => Ekind (Get_Type (N, Scope)) in Record_Kind | Private_Kind
                 and then Map_Root.Kind in Direct_Mapping | Record_Field
                 and then Nkind (Map_Type) in N_Defining_Identifier
                 and then Is_Type (Map_Type);
   --  Process a record or aggregate N and return a map which can be used
   --  to work out which fields will depend on what inputs.
   --
   --  Map_Root is used to produce keys for the map. For example if
   --     N         -->  (X => G, Y => H)
   --     Map_Root  -->  Tmp.F
   --
   --  Then we return:
   --     Tmp.F.X -> G
   --     Tmp.F.Y -> H
   --
   --  Scope, Local_Constants, Fold_Functions, Use_Computed_Globals,
   --  Expand_Synthesized_Constants will be passed on to Get_Variables
   --  if necessary.
   --
   --  Get_Variables will be called with Reduced set to False (as this
   --  function should never be called when its true...)

   function Untangle_Record_Fields
     (N                            : Node_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Expand_Synthesized_Constants : Boolean)
      return Flow_Id_Sets.Set
   with Pre => Nkind (N) = N_Selected_Component
               or else Is_Attribute_Update (N);
   --  Process a node describing one or more record fields and return a
   --  variable set with all variables referenced.
   --
   --  Fold_Functions also has an effect on how we deal with useless
   --  'Update expressions:
   --
   --     Node                 Fold_Functions  Result
   --     -------------------  --------------  --------
   --     R'Update (X => N).Y  False           {R.Y, N}
   --     R'Update (X => N).Y  True            {R.Y}
   --     R'Update (X => N)    False           {R.Y, N}
   --     R'Update (X => N)    True            {R.Y, N}
   --
   --  Scope, Local_Constants, Use_Computed_Globals,
   --  Expand_Synthesized_Constants will be passed on to Get_Variables if
   --  necessary.
   --
   --  Get_Variables will be called with Reduced set to False (as this function
   --  should never be called when it's true...)

   function Get_Precondition_Expressions (E : Entity_Id) return Node_Lists.List
   with Pre => Ekind (E) in Entry_Kind | E_Function | E_Procedure;
   --  Given the entity for a subprogram, return the expression(s) for its
   --  precondition and the condition(s) of its Contract_Cases (or return
   --  the empty list if none of these exist).

   function Get_Postcondition_Expressions (E       : Entity_Id;
                                           Refined : Boolean)
                                           return Node_Lists.List
   with Pre => Ekind (E) in Entry_Kind | E_Function | E_Package | E_Procedure;
   --  Given the entity for a subprogram or package, return all expression(s)
   --  associated with postconditions: the postcondition, the rhs for contract
   --  cases and the initial condition; or an empty list of none of these
   --  exist.

   function Is_Precondition_Check (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Pragma and then
               Get_Pragma_Id (N) = Pragma_Check;
   --  Given a check pragma, return if this is a precondition check

   function Contains_Discriminants
     (F : Flow_Id;
      S : Flow_Scope)
      return Boolean
   with Pre => F.Kind in Direct_Mapping | Magic_String;
   --  Returns true if the flattened variable for F contains at least one
   --  discriminant.

   function Is_Initialized_At_Elaboration (F : Flow_Id;
                                           S : Flow_Scope)
                                           return Boolean;
   --  Returns True iff F is covered by either a user-provided or a generated
   --  initializes aspect.
   --
   --  This function is a wrapper around Is_Initialized_At_Elaboration from
   --  Flow_Refinement and GG_Is_Initialized_At_Elaboration from
   --  Flow_Generated_Globals.

   function Is_Initialized_In_Specification (F : Flow_Id;
                                             S : Flow_Scope)
                                             return Boolean
   with Pre => Is_Initialized_At_Elaboration (F, S);
   --  Returns true for an entity which is initialized at elaboration *and*
   --  the initialization occurs in the specification of the enclosing
   --  package of F.

   procedure Add_Loop (E : Entity_Id)
   with Pre => Ekind (E) = E_Loop;
   --  Indicates that the loop E has been analyzed by flow analysis.

   procedure Add_Loop_Writes (Loop_E : Entity_Id;
                              Writes : Flow_Id_Sets.Set)
   with Pre => Ekind (Loop_E) = E_Loop;
   --  Adds Writes to the set of variables written by the loop entity Loop_E

   procedure Freeze_Loop_Info;
   --  Must be called at the end of flow analysis - this makes it an error to
   --  use Add_Loop and Add_Loop_Write, and enables the use of Get_Loop_Writes.

   function Loop_Writes_Known (E : Entity_Id) return Boolean
   with Pre => Ekind (E) = E_Loop;
   --  Checks if the variables written by loop E are known.

   function Get_Loop_Writes (E : Entity_Id) return Flow_Id_Sets.Set
   with Pre => Ekind (E) = E_Loop and then
               Loop_Writes_Known (E);
   --  Returns variables a given loop *may* write to, including variables
   --  declared locally in the loop. Note that if a function returns inside a
   --  loop, the name of the function will be "written to" and will be returned
   --  here.

   function Get_Type
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Entity_Id
   with Pre  => F.Kind in Direct_Mapping | Record_Field and then
                F.Facet = Normal_Part,
        Post => Is_Type (Get_Type'Result);
   --  @param F is the Flow_Id who's type we need to retrieve
   --  @param Scope is the scope relative to which we retrieve the type
   --  @return the entity corresponding to the type of F. If the full view
   --    of the type is not visible from Scope, then we return the non-full
   --    view.

   function Get_Type
     (N     : Node_Id;
      Scope : Flow_Scope)
      return Entity_Id
   with Pre  => Present (N),
        Post => (if Nkind (N) = N_Defining_Identifier and then
                    Ekind (N) = E_Abstract_State
                 then Get_Type'Result = Standard_Void_Type
                 else Is_Type (Get_Type'Result));
   --  @param N is the node who's type we need to retrieve
   --  @param Scope is the scope relative to which we retrieve the type
   --  @return the entity corresponding to the type of N. If the full view
   --    of the type is not visible from Scope, then we return the non-full
   --    view.

   function Get_Explicit_Formals (E : Entity_Id) return Node_Sets.Set
   with Pre  => Ekind (E) in E_Entry | E_Function | E_Procedure,
        Post => (for all F of Get_Explicit_Formals'Result => Is_Formal (F));
   --  Returns explicit formals of a subprogram or entry

   function Get_Implicit_Formal (E : Entity_Id) return Entity_Id
   with Pre => Ekind (E) in E_Entry | E_Function | E_Procedure | E_Task_Type,
        Post => (if Present (Get_Implicit_Formal'Result)
                 then Ekind (Get_Implicit_Formal'Result) in E_Protected_Type
                                                          | E_Task_Type);
   --  Returns implicit formals, i.e. the protected type for protected
   --  subprograms and entries and the task type itself for task types; returns
   --  Empty for ordinary subprograms.
   --  @param E is the entity of an entry/task/subprogram
   --  @return the implicit formal parameter of E, if any

   function Get_Formals (E : Entity_Id) return Node_Sets.Set
   with Pre  => Ekind (E) in E_Entry | E_Function | E_Procedure | E_Task_Type,
        Post => (for all F of Get_Formals'Result =>
                    Is_Formal (F)
                      or else
                    Ekind (F) in E_Protected_Type | E_Task_Type);
   --  Returns all implicit and explicit formal parameters of an Entry or
   --  Subprogram. For tasks it returns all discriminants of the task and
   --  the task itself.
   --  @param E is the entity of an entry/task/subprogram
   --  @return explicit and implicit formal parameters of E

   function Extensions_Visible (E     : Entity_Id;
                                Scope : Flow_Scope)
                                return Boolean
   with Pre => Ekind (E) in E_Abstract_State |
                            E_Function       |
                            E_Protected_Type |
                            E_Task_Type      |
                            Object_Kind;
   --  Checks if extensions are visible for this particular entity. Note that
   --  if we give it a function, then we always return false, since this refers
   --  to the 'Result of the function, not to the subprogram's aspect.
   --
   --  To check if a subprogram has the aspect, use the function
   --  Has_Extensions_Visible_Aspect from Flow_Tree_Utilities instead.
   --  ??? there is no such a function and even no such a package

   function Extensions_Visible (F     : Flow_Id;
                                Scope : Flow_Scope)
                                return Boolean
   with Pre => (if F.Kind in Direct_Mapping | Record_Field
                then Ekind (Get_Direct_Mapping_Id (F)) in E_Abstract_State |
                                                          E_Function       |
                                                          E_Protected_Type |
                                                          E_Task_Type      |
                                                          Object_Kind);
   --  As above, but using a Flow_Id

   function Search_Contract (Unit     : Entity_Id;
                             Contract : Pragma_Id;
                             Output   : Entity_Id;
                             Input    : Entity_Id := Empty)
                             return Node_Id
   with Pre  => Contract in Pragma_Depends | Pragma_Initializes
                and then Ekind (Output) in Assignable_Kind
                                         | E_Abstract_State
                                         | E_Constant
                                         | E_Function
                                         | E_Protected_Type
                                         | E_Task_Type
                and then (if Present (Input)
                          then Ekind (Input) in E_Abstract_State
                                              | E_Task_Type
                                              | Object_Kind),
        Post => Present (Search_Contract'Result);
   --  Search the Contract of Unit for the given Output. If Input is also
   --  given, search for that Input of the given Output. For now
   --  Search_Contract only works with either subprograms and pragma Depends
   --  or packages and pragma Initializes.
   --
   --  If we can't find what we're looking for, we return either the Unit
   --  itself or the corresponding contract (if it exists).

   function Replace_Flow_Ids
     (Of_This   : Entity_Id;
      With_This : Entity_Id;
      The_Set   : Flow_Id_Sets.Set)
      return Flow_Id_Sets.Set;
   --  Returns a flow set that replaces all Flow_Ids of The_Set that correspond
   --  to Of_This with equivalent Flow_Ids that correspond to With_This.
   --
   --  ??? this function is inefficient and its uses should be probably
   --  replaced with a call to Ada.Containers.Hashed_Sets.Replace_Element

   function Has_Variable_Input (C : Entity_Id) return Boolean
   with Pre => Ekind (C) = E_Constant;
   --  Returns True if V is a constant with variable input
   --
   --  If called before the globals graph has been generated then the results
   --  might not be accurate (this means that some constant that might not
   --  actually have variable input will be reported as having variable input).

   function Has_Bounds
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Boolean
   with Pre => (if F.Kind in Direct_Mapping | Record_Field
                  and then F.Facet = Normal_Part
                then Nkind (F.Node) in N_Entity);
   --  Returns True if a Flow_Id needs separate representation for its bounds

   function Is_Constituent (N : Node_Id) return Boolean;
   --  Returns True iff N is a constituent of an abstract state

   function Is_Abstract_State (N : Node_Id) return Boolean;
   --  Returns True iff N is an abstract state

   function Is_Ghost_Object (F : Flow_Id) return Boolean;
   --  Returns True iff F represents a ghost object
   --  ??? returns False if F.Kind = Magic_String, which is wrong; should be
   --  fixed by recording the ghost status in the ALI file.

   function Is_Variable (F : Flow_Id) return Boolean
   with Pre => Present (F);
   --  Returns True if F is either not a constant or is a constant
   --  with variable input.
   --  @param F is the Flow_Id that we check
   --  @return True if F is either not a constant or if it is a constant
   --     which Has_Variable_Input

   function Is_Empty_Record_Type (T : Entity_Id) return Boolean with
     Pre => No (T) or else Is_Type (T);
   --  Similar to Is_Null_Record_Type, but also returns true if this is a null
   --  extension of a null record type (or extension).

   function Canonical_Entity
     (Ref     : Entity_Id;
      Context : Entity_Id)
      return Entity_Id
   with Pre => Ekind (Context) in Entry_Kind
                                | E_Function
                                | E_Package
                                | E_Procedure
                                | E_Task_Type;
   --  Subsidiary to the parsing of contracts [Refined_]Depends, [Refined_]
   --  Global and Initializes. If entity Ref denotes the current instance of
   --  a concurrent type, as seen from Context, then returns the entity of that
   --  concurrent type; otherwise, returns Unique_Entity of E.

private
   Init_Done : Boolean := False;

   --------------------
   -- Is_Initialized --
   --------------------

   function Is_Initialized return Boolean is (Init_Done);

end Flow_Utility;
