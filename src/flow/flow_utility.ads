------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--              Copyright (C) 2013-2025, Capgemini Engineering              --
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

with Atree;                use Atree;
with Checked_Types;        use Checked_Types;
with Common_Containers;    use Common_Containers;
with Einfo.Entities;       use Einfo.Entities;
with Einfo.Utils;          use Einfo.Utils;
with Flow;                 use Flow;
with Flow_Dependency_Maps; use Flow_Dependency_Maps;
with Flow_Types;           use Flow_Types;
with Sem_Aux;              use Sem_Aux;
with Sem_Util;             use Sem_Util;
with Sinfo.Nodes;          use Sinfo.Nodes;
with Snames;               use Snames;
with SPARK_Util;           use SPARK_Util;
with Stand;                use Stand;
with Types;                use Types;

package Flow_Utility is

   procedure Pick_Generated_Info
     (N                  : Node_Id;
      Scop               : Flow_Scope;
      Function_Calls     : in out Call_Sets.Set;
      Indirect_Calls     : in out Node_Sets.Set;
      Proof_Dependencies : in out Node_Sets.Set;
      Tasking            : in out Tasking_Info;
      Generating_Globals : Boolean)
   with
     Pre  => Present (N),
     Post =>
       Function_Calls'Old.Is_Subset (Of_Set => Function_Calls)
       and then Proof_Dependencies'Old.Is_Subset
                  (Of_Set => Proof_Dependencies);
   --  For an expression N collect its called functions, proof dependencies and
   --  update the set of protected objects that are read-locked when evaluating
   --  these functions.
   --
   --  When Generating_Globals is set, then the implicit calls to predicate
   --  functions appear in the set of subprograms called. This is what we
   --  use in phase 1; in phase 2 this should not be set as we add the
   --  global effects directly.

   procedure Remove_Constants (Objects : in out Flow_Id_Sets.Set)
   with
     Post => Flow_Id_Sets.Is_Subset (Subset => Objects, Of_Set => Objects'Old);
   --  Remove from Objects all constants without variable input
   --  @param Objects are the initial flow ids

   function Is_Generic_Actual_Without_Variable_Input
     (E : Entity_Id) return Boolean;
   --  Returns True iff E is a constant that represents a generic actual
   --  parameter and has no variable input. Such constants are filtered from
   --  the Global/Depends/Initializes contract right when we parse the AST,
   --  because they are ignored both from the inside and from the outside of
   --  the generic instance; see SPARK RM 6.1.4(20):
   --
   --    "If a global_item denotes a generic formal object of mode in, then the
   --     corresponding global_item in an instance of the generic unit may
   --     denote a constant which has no variable inputs. [...] Outside of the
   --     instance, such a global_item is ignored."

   function Get_Flow_Id
     (Name : Entity_Name; View : Flow_Id_Variant := Normal_Use) return Flow_Id;
   --  Return a suitable Flow_Id for the entity name. We try our best to get a
   --  direct mapping, resorting to the magic string only if necessary.
   --  @param Name is the Entity_Name whose corresponding entity we
   --    are looking for
   --  @param View is the view that the returned Flow_Id will have
   --  @return a Flow_Id with either an entity or a magic_string if
   --    an entity cannot be found.

   function To_Flow_Id_Set
     (NS : Name_Sets.Set; View : Flow_Id_Variant := Normal_Use)
      return Flow_Id_Sets.Set;
   --  Converts a name set into a flow id set. The flow ids have their views
   --  set to View.
   --  @param NS is the name set that will be converted
   --  @param View is the view that flow ids will be given
   --  @return the equivalent set of flow ids

   function Has_Depends (Subprogram : Entity_Id) return Boolean
   with
     Pre =>
       Ekind (Subprogram) in E_Entry | E_Function | E_Procedure | E_Task_Type;
   --  Return true if the given subprogram has been annotated with a dependency
   --  relation.

   procedure Get_Depends
     (Subprogram           : Runnable_Kind_Id;
      Scope                : Flow_Scope;
      Classwide            : Boolean;
      Depends              : out Dependency_Maps.Map;
      Use_Computed_Globals : Boolean := True)
   with
     Pre  =>
       Ekind (Subprogram) in E_Entry | E_Function | E_Procedure | E_Task_Type
       and then Has_Depends (Subprogram),
     Post =>
       (for all Inputs of Depends =>
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

   procedure Get_Globals
     (Subprogram          : Runnable_Kind_Id;
      Scope               : Flow_Scope;
      Classwide           : Boolean;
      Globals             : out Global_Flow_Ids;
      Use_Deduced_Globals : Boolean := True;
      Ignore_Depends      : Boolean := False)
   with
     Pre  =>
       Ekind (Subprogram) in E_Entry | E_Function | E_Procedure | E_Task_Type
       and then not Is_Derived_Type (Subprogram)
       and then (if Ekind (Subprogram) = E_Procedure
                 then
                   not Is_DIC_Procedure (Subprogram)
                   and then not Is_Invariant_Procedure (Subprogram)
                 elsif Ekind (Subprogram) = E_Function
                 then not Is_Predicate_Function (Subprogram)),
     Post =>
       (for all G of Globals.Proof_Ins =>
          Is_Entire_Variable (G) and then G.Variant = In_View)
       and then (for all G of Globals.Inputs =>
                   Is_Entire_Variable (G) and then G.Variant = In_View)
       and then (for all G of Globals.Outputs =>
                   Is_Entire_Variable (G) and then G.Variant = Out_View);
   --  Given a subprogram, work out globals from the appropriate global aspect
   --  (relative to Scope), or the depends aspect (if no global aspect is
   --  given). If the Global and Depends aspects are not present then use
   --  the generated globals. The sets returned will contain Flow_Id with
   --  the variant set to In_View and Out_View.
   --
   --  This query is meaningless for derived task types (whose entities are
   --  also of an E_Task_Type kind), because derived types cannot be annotated
   --  with a Global/Depends contracts.
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

   procedure Get_Proof_Globals
     (Subprogram      : Runnable_Kind_Id;
      Reads           : out Flow_Id_Sets.Set;
      Writes          : out Flow_Id_Sets.Set;
      Erase_Constants : Boolean;
      Scop            : Flow_Scope := Null_Flow_Scope)
   with
     Post =>
       (for all G of Reads =>
          Is_Entire_Variable (G) and then G.Variant = Normal_Use)
       and then (for all G of Writes =>
                   Is_Entire_Variable (G) and then G.Variant = Normal_Use);
   --  Same as above but Reads consists of both the Reads and Proof_Ins,
   --  discriminants receive no special handling and globals are proof globals,
   --  and we always return the most refined view possible. If Keep_Constants
   --  is true then constants with variable inputs are not suppressed form the
   --  Globals even if they are constants in Why. For subprograms nested in
   --  protected types, which may have an effect on the components of the
   --  protected type, the protected type itself is returned as a global.
   --
   --  If the Scop paramter is present, then visibility of Refined_Global will
   --  be respected; this is needed when the result will be used together with
   --  the result of Get_Loop_Writes, which itself respects visibility (by the
   --  way it is implemented). Otherwise, return Refined_Global iff subprogram
   --  body is in SPARK and Global if only spec is in SPARK.

   function Is_Opaque_For_Proof (F : Flow_Id) return Boolean
   with Pre => F.Kind = Magic_String, Ghost;
   --  Returns True iff the internal structure of F is not visible to proof

   function Rely_On_Generated_Global
     (E : Entity_Id; Scope : Flow_Scope) return Boolean
   with Pre => Ekind (E) in E_Entry | E_Function | E_Procedure | E_Task_Type;
   --  Returns True if Scope has visibility of E's body and Generated Globals
   --  will be produced for E.

   function Get_Functions
     (N : Node_Id; Include_Predicates : Boolean) return Node_Sets.Set
   with Pre => Nkind (N) in N_Subexpr;
   --  Collect functions called in an expression N. If Include_Predicates is
   --  True, then also include implicit calls to predicate functions.

   function Get_Variables
     (N                       : Node_Id;
      Scope                   : Flow_Scope;
      Target_Name             : Flow_Id;
      Fold_Functions          : Reference_Kind;
      Use_Computed_Globals    : Boolean;
      Assume_In_Expression    : Boolean := True;
      Expand_Internal_Objects : Boolean := False;
      Consider_Extensions     : Boolean := False;
      Skip_Old                : Boolean := False) return Flow_Id_Sets.Set;
   --  Obtain all variables used in an expression; use Scope to determine if
   --  called subprograms should provide their abstract or refined view.
   --
   --  When processing the RHS of an assignment statement with an '@' symbol,
   --  the Target_Name is the object being assigned (the LHS); otherwise, it
   --  is Null_Flow_Id.
   --
   --  ??? Fold_Functions parameter refers to previous handling of objects
   --  referenced in assertions and null dependencies; should be renamed.
   --
   --  The following other options all have default parameters as they are only
   --  useful in certain usage scenarios. In the majority of flow analysis, one
   --  does not have to think about them. They are:
   --
   --     * Assume_In_Expression: if True, we assume that node N is part of
   --       some kind of expression, and aggressively raise exceptions if we
   --       find nodes that make no sense in such a context.
   --
   --     * Expand_Internal_Objects: if True, then constants that do not come
   --       from source (i.e. constants that capture variables) are expanded to
   --       the variables referenced in their initialization expression;
   --       similar for variables that come from inlining-for-proof.
   --
   --     * Skip_Old: if True, then the prefix of references to the Old
   --       attribute are skipped.

   function Get_Variables_For_Proof
     (Expr_N : Node_Id; Scope_N : Node_Id; Skip_Old : Boolean := False)
      return Flow_Id_Sets.Set
   with
     Pre  => Nkind (Expr_N) in N_Subexpr and then Present (Scope_N),
     Post =>
       (for all F of Get_Variables_For_Proof'Result =>
          Is_Entire_Variable (F) and then F.Variant = Normal_Use);
   --  A wrapper around Get_Variables, as used by proof. Expr_N is the
   --  expression for which we obtain variables, and Scope_N is the node
   --  controlling visibility.

   function Get_All_Variables
     (N                       : Node_Id;
      Scope                   : Flow_Scope;
      Target_Name             : Flow_Id;
      Use_Computed_Globals    : Boolean;
      Assume_In_Expression    : Boolean := True;
      Expand_Internal_Objects : Boolean := False;
      Skip_Old                : Boolean := False) return Flow_Id_Sets.Set;
   --  Returns variables referenced by N in all modes, i.e. inputs, proof_ins
   --  and null dependencies.

   function Get_Components
     (F : Flow_Id; Scope : Flow_Scope) return Flow_Id_Sets.Set
   with Pre => Present (F);
   --  Splits F into components.
   --
   --  For types other than those mentioned below, we just return F.
   --
   --  For record types, we return the visible components (including the
   --  discriminants) of F (or F itself if there isn't any visible component or
   --  non null private part) together with F'Extension_Part if F has a
   --  classwide type or with F'Private_Part if F has a non null private part
   --  or if its type derives from a private type.
   --
   --  For simple private types we return F. For private types with
   --  discriminant C, we return F.C and F'Private_Part.
   --
   --  @param F is the Flow_Id whose components we need to gather
   --  @param Scope is the scope relative to which we will return the
   --         components
   --  @return the components of F that are visible from Scope.

   function Flatten_Variable
     (F : Flow_Id; Scope : Flow_Scope) return Flow_Id_Sets.Set
   with Pre => Present (F);
   --  Iteratively calls Get_Components to return all the subcomponents of F.
   --
   --  @param F is the Flow_Id whose subcomponents we need to gather
   --  @param Scope is the scope relative to which we will return the
   --         subcomponents
   --  @return all subcomponents of F that are visible from Scope.

   function Flatten_Variable
     (E : Entity_Id; Scope : Flow_Scope) return Flow_Id_Sets.Set
   is (Flatten_Variable (Direct_Mapping_Id (Unique_Entity (E)), Scope))
   with
     Pre =>
       Ekind (E) in E_Abstract_State | E_Function | Object_Kind | Type_Kind;
   --  As above, but conveniently taking an Entity_Id instead of a Flow_Id

   function Expand_Abstract_States
     (Vars : Flow_Id_Sets.Set) return Flow_Id_Sets.Set;
   --  Recursively expands abstract states in Vars to their constituents, so
   --  that all flow-to-proof queries provide consistent view of abstract
   --  states and their constituent.

   subtype Valid_Assignment_Kinds is Node_Kind
   with
     Static_Predicate =>
       Valid_Assignment_Kinds
       in N_Identifier
        | N_Expanded_Name
        | N_Type_Conversion
        | N_Unchecked_Type_Conversion
        | N_Indexed_Component
        | N_Slice
        | N_Explicit_Dereference
        | N_Selected_Component;

   function Is_Valid_Assignment_Target (N : Node_Id) return Boolean
   with
     Post =>
       (if Is_Valid_Assignment_Target'Result
        then Nkind (N) in Valid_Assignment_Kinds),
     Ghost;
   --  Returns True if the tree under N is a combination of
   --  Valid_Assignment_Kinds only.

   procedure Get_Assignment_Target_Properties
     (N                  : Node_Id;
      Scope              : Flow_Scope;
      Partial_Definition : out Boolean;
      View_Conversion    : out Boolean;
      Map_Root           : out Flow_Id;
      Seq                : out Node_Lists.List)
   with
     Pre  => Is_Valid_Assignment_Target (N),
     Post =>
       Map_Root.Kind in Direct_Mapping | Record_Field
       and then (for all X of Seq => Nkind (X) in Valid_Assignment_Kinds);
   --  Checks the assignment target N and determines a few basic properties
   --
   --  * Partial_Definition: the assignment to N touches only a few elements
   --                        of a larger object. For assignments into view
   --                        conversions, Partial_Definition can be set to
   --                        False even though the whole target is not updated.
   --                        The caller is responsible for deciding which
   --                        components are effectively updated.
   --  * View_Conversion: N contains a view conversion.
   --  * Map_Root: the non-flattened Flow_Id which is assigned to.
   --  * Seq: items used to derive Map_Root.

   procedure Untangle_Assignment_Target
     (N                    : Node_Id;
      Scope                : Flow_Scope;
      Use_Computed_Globals : Boolean;
      Force_Extension      : Boolean := False;
      View_Conversion      : out Boolean;
      Map_Root             : out Flow_Id;
      Vars_Defined         : out Flow_Id_Sets.Set;
      Vars_Used            : out Flow_Id_Sets.Set;
      Partial_Definition   : out Boolean;
      Partial_Ext          : out Boolean;
      Partial_Priv         : out Boolean)
   with
     Pre  => Is_Valid_Assignment_Target (N),
     Post =>
       (if not Is_Empty_Record_Type (Etype (N)) then not Vars_Defined.Is_Empty)
       and then not (Partial_Definition and (Partial_Ext or Partial_Priv));
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
   --     - pointer dereference
   --
   --  Note that the expression(s) in the index or slice can be much more
   --  general and thus will be processed by Get_Variables.
   --
   --  Note we only support unchecked conversion from and to scalars, i.e.
   --  for things generated from:
   --     Foo (Positive (X))
   --
   --  Map_Root, View_Conversion, and Partial are the values returned by
   --  Get_Assignment_Target_Properties.
   --
   --  If the object is entirely written except its extension part or private
   --  part, Partial_Definition is set to False but Partial_Ext and/or
   --  Partial_Priv be True.
   --
   --  If Force_Extension is True, N is an actual of a call to a subprogram
   --  with extension visible. The extension will be set even if the
   --  type of the actual is not classwide.

   function Untangle_Record_Assignment
     (N                       : Node_Id;
      Map_Root                : Flow_Id;
      Map_Type                : Entity_Id;
      Target_Name             : Flow_Id;
      Scope                   : Flow_Scope;
      Fold_Functions          : Reference_Kind;
      Use_Computed_Globals    : Boolean;
      Expand_Internal_Objects : Boolean;
      Extensions_Irrelevant   : Boolean;
      Top_Level               : Boolean := True) return Flow_Id_Maps.Map
   with
     Pre =>
       Ekind (Get_Type (N, Scope)) in Record_Kind | Private_Kind
       and then Map_Root.Kind in Direct_Mapping | Record_Field
       and then Is_Type (Map_Type);
   --  Process a record or aggregate N and return a map which can be used to
   --  work out which fields will depend on what inputs.
   --
   --  Map_Root is used to produce keys for the map. For example if
   --     N         -->  (X => G, Y => H)
   --     Map_Root  -->  Tmp.F
   --
   --  Then we return:
   --     Tmp.F.X -> G
   --     Tmp.F.Y -> H
   --
   --  Target_Name is the object represented by '@' on the RHS of an assignment
   --  statements or Null_Flow_Id if '@' is not expected.
   --
   --  Scope, Fold_Functions, Use_Computed_Globals, Expand_Internal_Objects
   --  will be passed on to Get_Variables if necessary.
   --
   --  If Top_Level is True, introduce a conversion to the type of Map_Root.

   function Get_Precondition_Expressions (E : Entity_Id) return Node_Lists.List
   with
     Pre =>
       Ekind (E) in Entry_Kind | E_Function | E_Procedure | E_Subprogram_Type;
   --  Given the entity for a subprogram, return the expression(s) for its
   --  precondition and the condition(s) of its Contract_Cases (or return
   --  the empty list if none of these exist).

   function Get_Postcondition_Expressions
     (E : Entity_Id; Refined : Boolean) return Node_Lists.List
   with
     Pre =>
       Ekind (E)
       in Entry_Kind
        | E_Function
        | E_Package
        | E_Procedure
        | E_Subprogram_Type;
   --  Given the entity for a subprogram or package, return all expression(s)
   --  associated with postconditions: the postcondition, the rhs for contract
   --  cases and the initial condition; or an empty list of none of these
   --  exist.

   function Calls_Dispatching_Equality (N : Node_Id) return Boolean
   with
     Pre =>
       Nkind (N) in N_Function_Call | N_Membership_Test | N_Op_Eq | N_Op_Ne;
   --  Returns True iff N indirectly calls a dispatching equality

   function Is_Initialized_At_Elaboration
     (F : Flow_Id; S : Flow_Scope) return Boolean;
   --  Returns True iff F is covered by either a user-provided or a generated
   --  initializes aspect.
   --
   --  This function is a wrapper around Is_Initialized_At_Elaboration from
   --  Flow_Refinement and GG_Is_Initialized_At_Elaboration from
   --  Flow_Generated_Globals.

   function Is_Initialized_In_Specification
     (F : Flow_Id; S : Flow_Scope) return Boolean
   with Pre => Is_Initialized_At_Elaboration (F, S);
   --  Returns true for an entity which is initialized at elaboration *and*
   --  the initialization occurs in the specification of the enclosing
   --  package of F.

   procedure Add_Loop_Writes (Loop_E : Entity_Id; Writes : Flow_Id_Sets.Set)
   with Pre => Ekind (Loop_E) = E_Loop;
   --  Adds Writes to the set of variables written by the loop entity Loop_E

   procedure Freeze_Loop_Info
   with Ghost;
   --  Must be called at the end of flow analysis - this makes it an error to
   --  use Add_Loop and Add_Loop_Write, and enables the use of Get_Loop_Writes.

   function Get_Loop_Writes (E : Entity_Id) return Flow_Id_Sets.Set
   with
     Pre  => Ekind (E) = E_Loop,
     Post =>
       (for all F of Get_Loop_Writes'Result =>
          Is_Entire_Variable (F) and then F.Variant = Normal_Use);
   --  Returns variables a given loop *may* write to, including variables
   --  declared locally in the loop. Note that if a function returns inside a
   --  loop, the name of the function will be "written to" and will be returned
   --  here.

   function Get_Type (F : Flow_Id; Scope : Flow_Scope) return Entity_Id
   with
     Pre  =>
       F.Kind in Direct_Mapping | Record_Field and then F.Facet = Normal_Part,
     Post => Is_Type (Get_Type'Result);
   --  @param F is the Flow_Id who's type we need to retrieve
   --  @param Scope is the scope relative to which we retrieve the type
   --  @return the entity corresponding to the type of F. If the full view
   --    of the type is not visible from Scope, then we return the non-full
   --    view.

   function Get_Type (N : Node_Id; Scope : Flow_Scope) return Entity_Id
   with
     Pre  => Nkind (N) in N_Entity | N_Subexpr,
     Post =>
       (if Nkind (N) = N_Defining_Identifier
          and then Ekind (N) = E_Abstract_State
        then Get_Type'Result = Standard_Void_Type
        else Is_Type (Get_Type'Result));
   --  @param N either an entity or a subexpression
   --  @param Scope is the scope relative to which we retrieve the type
   --  @return the entity corresponding to the type of N. If the full view
   --    of the type is not visible from Scope, then we return the non-full
   --    view.

   function Get_Explicit_Formals (E : Entity_Id) return Node_Sets.Set
   with
     Pre  =>
       Ekind (E) in E_Entry | E_Function | E_Procedure | E_Subprogram_Type,
     Post => (for all F of Get_Explicit_Formals'Result => Is_Formal (F));
   --  Returns explicit formals of a subprogram or entry

   function Get_Implicit_Formal (E : Entity_Id) return Entity_Id
   with
     Pre  => Ekind (E) in E_Entry | E_Function | E_Procedure | E_Task_Type,
     Post =>
       (if Present (Get_Implicit_Formal'Result)
        then
          Ekind (Get_Implicit_Formal'Result)
          in E_Protected_Type | E_Task_Type);
   --  Returns implicit formals, i.e. the protected type for protected
   --  subprograms and entries and the task type itself for task types; returns
   --  Empty for ordinary subprograms.
   --  @param E is the entity of an entry/task/subprogram
   --  @return the implicit formal parameter of E, if any

   function Get_Formals (E : Entity_Id) return Node_Sets.Set
   with
     Pre  => Ekind (E) in E_Entry | E_Function | E_Procedure | E_Task_Type,
     Post =>
       (for all F of Get_Formals'Result =>
          Is_Formal (F) or else Ekind (F) in E_Protected_Type | E_Task_Type);
   --  Returns all implicit and explicit formal parameters of an Entry or
   --  Subprogram. For tasks it returns all discriminants of the task and
   --  the task itself.
   --  @param E is the entity of an entry/task/subprogram
   --  @return explicit and implicit formal parameters of E

   function Extensions_Visible
     (E : Entity_Id; Scope : Flow_Scope) return Boolean
   with
     Pre =>
       Ekind (E)
       in E_Abstract_State
        | E_Function
        | E_Protected_Type
        | E_Task_Type
        | Object_Kind;
   --  Checks if extensions are visible for this particular entity. Note that
   --  if we give it a function, then we always return false, since this refers
   --  to the 'Result of the function, not to the subprogram's aspect.
   --
   --  To check if a subprogram has the aspect, use the function
   --  Has_Extensions_Visible_Aspect from Flow_Tree_Utilities instead.
   --  ??? there is no such a function and even no such a package

   function Extensions_Visible (F : Flow_Id; Scope : Flow_Scope) return Boolean
   with
     Pre =>
       (if F.Kind in Direct_Mapping | Record_Field
        then
          Ekind (Get_Direct_Mapping_Id (F))
          in E_Abstract_State
           | E_Function
           | E_Protected_Type
           | E_Task_Type
           | Object_Kind);
   --  As above, but using a Flow_Id

   function Search_Depends_Contract
     (Unit : Entity_Id; Output : Entity_Id; Input : Entity_Id := Empty)
      return Node_Id
   with
     Pre  =>
       Ekind (Unit) in E_Function | E_Procedure | E_Entry | E_Task_Type
       and then (No (Output)
                 or else Ekind (Output)
                         in Assignable_Kind
                          | E_Abstract_State
                          | E_Constant
                          | E_In_Parameter
                          | E_Function
                          | E_Protected_Type
                          | E_Task_Type)
       and then (if Present (Input)
                 then
                   Ekind (Input)
                   in E_Abstract_State
                    | E_Task_Type
                    | E_Protected_Type
                    | Object_Kind),
     Post => Present (Search_Depends_Contract'Result);
   --  Search the Contract of Unit for the given "Output => Input" dependency.
   --
   --  If we can't find what we're looking for, we return either the Unit
   --  itself or the corresponding contract (if it exists).

   function Search_Initializes_Contract
     (Unit : Entity_Id; Output : Entity_Id; Input : Entity_Id := Empty)
      return Node_Id
   with
     Pre  =>
       Ekind (Unit) = E_Package
       and then Ekind (Output) in E_Variable | E_Abstract_State | E_Constant
       and then (if Present (Input)
                 then
                   Ekind (Input)
                   in E_Abstract_State | E_Task_Type | Object_Kind),
     Post => Present (Search_Initializes_Contract'Result);
   --  Same as Search_Depends_Contract, but for the Initializes contract

   function Has_Variable_Input (C : Entity_Id) return Boolean
   with
     Pre => Ekind (C) = E_Constant and then not Is_Access_Variable (Etype (C));
   --  Returns True if V is a constant with variable input
   --
   --  If this is called before the globals graph has been generated (i.e.
   --  completion of phase 1) the results might not be accurate. The function
   --  may erroneously report that some constant does have variable input when
   --  it might not actually have variable input.

   function Has_Bounds (F : Flow_Id; Scope : Flow_Scope) return Boolean
   with
     Pre =>
       (if F.Kind in Direct_Mapping | Record_Field
          and then F.Facet = Normal_Part
        then Nkind (F.Node) in N_Entity);
   --  Returns True if a Flow_Id needs separate representation for its bounds

   function Ignore_Record_Type_Discriminants
     (Vars_Used : Flow_Id_Sets.Set) return Flow_Id_Sets.Set
   with
     Post =>
       Ignore_Record_Type_Discriminants'Result.Is_Subset (Of_Set => Vars_Used);
   --  Filters out all <Record Type>.Discriminant constructs returned from
   --  Get_Variables when recursing into the default expression of a record
   --  component.

   function Is_Constituent (N : Node_Id) return Boolean;
   --  Returns True iff N is a constituent of an abstract state

   function Is_Implicit_Constituent (N : Node_Id) return Boolean;
   --  Returns True iff N is implicitly lifted to a singleton abstract state

   function Is_Abstract_State (N : Node_Id) return Boolean;
   --  Returns True iff N is an abstract state

   function Is_Dummy_Abstract_State
     (F : Flow_Id; S : Flow_Scope) return Boolean;
   --  Returns True if F is an abstract state that, when looking from S, can
   --  be determined to have no constituents. Such abstract states are most
   --  likely just placeholders and will be later removed or populated with
   --  constituents.

   function Is_Ghost_Entity (F : Flow_Id) return Boolean;
   --  Returns True iff F represents a ghost entity

   function Is_Checked_Ghost_Entity (F : Flow_Id) return Boolean;
   --  Returns True iff F represents a ghost entity with policy Checked

   function Is_Constant_After_Elaboration (F : Flow_Id) return Boolean
   with Pre => Present (F);
   --  Returns True iff F represents a constant after elaboration

   function Is_Variable (F : Flow_Id) return Boolean
   with Pre => Present (F);
   --  Returns whether F represents a variable in flow.
   --  @param F is the Flow_Id that we check
   --  @return True if F is either not a constant or a constant of access type
   --     or a constant with variable input.

   function Is_Empty_Record_Type (T : Entity_Id) return Boolean
   with Pre => No (T) or else Is_Type (T);
   --  Similar to Is_Null_Record_Type, but also returns true if this is a null
   --  extension of a null record type (or extension).
   --  ??? I think it should also return True for a record whose all components
   --  are empty.

   type Raw_Global_Nodes is record
      Proof_Ins : Node_Sets.Set;
      Inputs    : Node_Sets.Set;
      Outputs   : Node_Sets.Set;
   end record
   with
     Dynamic_Predicate =>
       (for all G of Raw_Global_Nodes.Proof_Ins =>
          not Raw_Global_Nodes.Inputs.Contains (G)
          and then not Raw_Global_Nodes.Outputs.Contains (G));
   --  Represents Global/Refined_Global as it appears in the source code;
   --  unlike Global_Nodes, it may contain constants without variable inputs.

   function Parse_Global_Contract
     (Subprogram : Entity_Id; Global_Node : Node_Id) return Raw_Global_Nodes
   with
     Pre =>
       Ekind (Subprogram) in E_Function | E_Procedure | E_Entry | E_Task_Type
       and then Nkind (Global_Node) = N_Pragma
       and then Get_Pragma_Id (Global_Node)
                in Pragma_Global | Pragma_Refined_Global;
   --  Returns Global/Refined_Global, as they appear in the source code; in
   --  particular, without down-projections or trimming done by Get_Globals,
   --  which returns the global contract adapted for the use in flow graphs.

   function Parse_Depends_Contract
     (Subprogram : Entity_Id; Depends_Node : Node_Id) return Raw_Global_Nodes
   with
     Pre =>
       Ekind (Subprogram) in E_Function | E_Procedure | E_Entry | E_Task_Type
       and then Nkind (Depends_Node) = N_Pragma
       and then Get_Pragma_Id (Depends_Node)
                in Pragma_Depends | Pragma_Refined_Depends;
   --  Returns Depends/Refined_Depends, as they appear in the source code; in
   --  particular, without down-projections or trimming done by Get_Depends,
   --  which returns the depends contract adapted for the use in flow graphs.

   function Contract_Globals (E : Entity_Id) return Raw_Global_Nodes
   with Pre => Ekind (E) in E_Function | E_Procedure | E_Entry | E_Task_Type;
   --  Returns globals as they appear in the Global/Depends contract (or their
   --  refined variants, if available). This is useful when dealing with
   --  partially-visible abstract states where an object in the flow graph
   --  might be represented in the contract either directly or via its abstract
   --  state.

   function Find_In (User : Node_Sets.Set; G : Entity_Id) return Entity_Id
   with
     Post => (if Present (Find_In'Result) then User.Contains (Find_In'Result));
   --  If a global G is represented by User ones, either directly or via an
   --  abstract state, then return the representative user global; otherwise
   --  return Empty.

   function Find_In (User : Flow_Id_Sets.Set; G : Flow_Id) return Flow_Id
   with
     Post => (if Present (Find_In'Result) then User.Contains (Find_In'Result));
   --  Same as above but for Flow_Ids; returns Null_Flow_Id instead of Empty

   procedure Map_Generic_In_Formals
     (Scop    : Flow_Scope;
      Objects : in out Flow_Id_Sets.Set;
      Entire  : Boolean := True);
   --  Map generic IN formal parameters, which are visible inside of generic
   --  instances (e.g. might appear in Global and Initializes contracts) into
   --  objects used in their corresponding generic actual parameter expression.
   --
   --  If Entire is True, then map to the entire objects; if it is False, then
   --  map to individual components referenced in the actual parameter.
   --  ??? This parameter should be removed and the callers should use
   --  To_Entire_Variables if needed, but this would be a bit ugly as well.

   function Strip_Child_Prefixes (EN : String) return String;
   --  Strip Child_Prefix from the string representation of an Entity_Name

   function Path_To_Flow_Id (Expr : Node_Id; Scop : Flow_Scope) return Flow_Id
   with
     Pre  => Is_Path_Expression (Expr),
     Post =>
       (if Present (Path_To_Flow_Id'Result)
        then
          Path_To_Flow_Id'Result.Kind in Direct_Mapping | Record_Field
          and then Path_To_Flow_Id'Result.Variant = Normal_Use);
   --  Converts a "path expression", which is how objects are represented in
   --  the borrow checker, to a "flow_id", which is how objects are represented
   --  in flow.
   --
   --  Note: this routine is similar to Get_Assignment_Target_Properties,
   --  but only returns the Flow_Id and not the properties. Also, it handles
   --  qualified expressions, which cannot appear in the assignment target. In
   --  short, this routine can be used both for the LHS and RHS of assignments,
   --  while Get_Assignment_Target_Properties can be only used for the LHS.

   function Termination_Proved
     (I_Scheme           : Opt_N_Iteration_Scheme_Id;
      Loop_Writes        : Flow_Id_Sets.Set;
      Generating_Globals : Boolean := False) return Boolean;
   --  Analyzes an iteration scheme, if present, to determine whether
   --  termination of the loop is guaranteed either by its syntax or by
   --  the semantics of its iteration scheme.

   function To_Subprograms (Calls : Call_Sets.Set) return Node_Sets.Set;
   --  Convert calls to called entities

   function Called_Primitive_Equalities
     (Ty : Entity_Id; Force_Predef : Boolean := False) return Node_Sets.Set;
   --  Return the set of user-defined equalities called by the primitive
   --  equality of Ty. If Force_Predef is True, use the predefined equality
   --  even if Ty is a type on which Ada equality uses the primitive equality.

   function Get_Outputs_From_Program_Exit
     (E : Entity_Id; Scop : Node_Id) return Flow_Id_Sets.Set
   with Pre => Is_Subprogram (E);
   --  Compute the set of outputs of E mentioned in its exit postcondition

   function Get_Outputs_From_Program_Exit
     (E : Entity_Id; Scope : Flow_Scope; Use_Computed_Globals : Boolean)
      return Flow_Id_Sets.Set
   with Pre => Is_Subprogram (E);
   --  Return global outputs used in the Program_Exit expression; for flow

private

   procedure Process_Type_Contracts_Internal
     (Typ                : Type_Kind_Id;
      Scop               : Flow_Scope;
      Include_Invariant  : Boolean;
      Proof_Dependencies : in out Node_Sets.Set;
      Types_Seen         : in out Node_Sets.Set;
      Constants_Seen     : in out Node_Sets.Set)
   with Post => Proof_Dependencies'Old.Is_Subset (Proof_Dependencies);
   --  Like Process_Type_Contracts, with additional parameters Types_Seen and
   --  Constants_Seen that allows to track which type predicates and constant
   --  expressions we already traversed to pick proof dependencies.

end Flow_Utility;
