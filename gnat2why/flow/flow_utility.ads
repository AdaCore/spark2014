------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2013-2015, Altran UK Limited                 --
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

--  This package contains a bunch of helpful procedures used
--  throughout flow analysis.

with Ada.Containers;

with Types;                use Types;
with Einfo;                use Einfo;
with Sem_Util;             use Sem_Util;
with Snames;               use Snames;
with Sinfo;                use Sinfo;
with Atree;                use Atree;

with Common_Containers;    use Common_Containers;

with Flow_Dependency_Maps; use Flow_Dependency_Maps;
with Flow_Refinement;      use Flow_Refinement;
with Flow_Tree_Utility;    use Flow_Tree_Utility;
with Flow_Types;           use Flow_Types;

use type Ada.Containers.Count_Type;

package Flow_Utility is

   function Get_Flow_Id
     (Name : Entity_Name;
      View : Parameter_Variant)
      return Flow_Id;
   --  Return a suitable flow id for the unique_name of an entity. We
   --  try our best to get a direct mapping, resorting to the magic
   --  string only as a last resort.

   function Get_Full_Type
     (N     : Node_Id;
      Scope : Flow_Scope)
      return Entity_Id
     with Pre => Present (N);
   --  Get the type of the given node. If the full view of the type
   --  is not visible from Scope, then we return the non-full view.

   function Has_Depends (Subprogram : Entity_Id) return Boolean
     with Pre => Ekind (Subprogram) in Subprogram_Kind;
   --  Return true if the given subprogram has been annotated with a
   --  dependency relation.

   procedure Get_Depends
     (Subprogram           : Entity_Id;
      Scope                : Flow_Scope;
      Classwide            : Boolean;
      Depends              : out Dependency_Maps.Map;
      Use_Computed_Globals : Boolean := True)
     with Pre  => Ekind (Subprogram) in Subprogram_Kind and
                  Has_Depends (Subprogram),
          Post => (for all C in Depends.Iterate =>
                     (for all D of Dependency_Maps.Element (C) =>
                        Present (D)));
   --  Return the dependency relation of the given Subprogram, as viewed
   --  from the given Scope. The dependency relation is represented as a
   --  map from entities to sets of entities.
   --
   --  For example (X, Y) =>+ Z would be represented as:
   --     x -> {x, z}
   --     y -> {y, z}
   --
   --  This procedure can deal with all forms of the depends
   --  annotation. For each item in the dependency annotation, the LHS
   --  and RHS can be any of the following:
   --     * (x, y, z)     (an aggregate)
   --     * x             (a variable)
   --     * null          (keyword null)
   --  One final form which is supported is the null dependency.
   --
   --  The + shorthand to mean "itself" is expanded away by the
   --  front-end and this procedure does not have to deal with it.
   --
   --  The Use_Computed_Globals flag is set to False during the
   --  generation of globals phase. It prevents us from attempting to
   --  use generated glboals before they have actually been produced.

   procedure Get_Globals (Subprogram             : Entity_Id;
                          Scope                  : Flow_Scope;
                          Classwide              : Boolean;
                          Proof_Ins              : out Flow_Id_Sets.Set;
                          Reads                  : out Flow_Id_Sets.Set;
                          Writes                 : out Flow_Id_Sets.Set;
                          Consider_Discriminants : Boolean := False;
                          Globals_For_Proof      : Boolean := False;
                          Use_Computed_Globals   : Boolean := True)
     with Pre  => Ekind (Subprogram) in E_Procedure | E_Function,
          Post => (for all G of Proof_Ins => G.Variant = In_View) and
                  (for all G of Reads     => G.Variant = In_View) and
                  (for all G of Writes    => G.Variant = Out_View);
   --  Given a subprogram call, work out globals from the appropriate
   --  global aspect (relative to Scope), or the depends aspect (if no
   --  global aspect is given). If the Global and Depends aspects are
   --  not present then use the generated globals or finally, if non
   --  of the above exist fall back to the computed globals. The sets
   --  returned will contain Flow_Id with the variant set to In_View
   --  and Out_View.
   --
   --  If Consider_Discriminants is provided then an out global will
   --  include a corresponding read if the global includes at least
   --  one discriminant.
   --
   --  If Globals_For_Proof is set then the calls to
   --  Get_Generated_Reads will not specify Include_Constants.

   procedure Get_Proof_Globals (Subprogram           : Entity_Id;
                                Classwide            : Boolean;
                                Reads                : out Flow_Id_Sets.Set;
                                Writes               : out Flow_Id_Sets.Set;
                                Use_Computed_Globals : Boolean := True)
     with Pre  => Ekind (Subprogram) in E_Procedure | E_Function,
          Post => (for all G of Reads  => G.Variant = In_View) and
                  (for all G of Writes => G.Variant = Out_View);
   --  Same as above but Reads consists of both the Reads and Proof_Ins,
   --  discriminants receive no special handling and globals are proof
   --  globals, and we always return the most refined view possible.

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
     (Subprogram : Entity_Id;
      Scope      : Flow_Scope)
      return Boolean;
   --  Returns True if Scope has visibility of Subprogram's body and
   --  Generated Globals will be produced for Subprogram.

   function Get_Function_Set (N : Node_Id) return Node_Sets.Set;
   --  Obtains all function calls used in an expression.

   function Get_Variable_Set
     (N                            : Node_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Allow_Statements             : Boolean := False;
      Expand_Synthesized_Constants : Boolean := False;
      Consider_Extensions          : Boolean := False)
      return Flow_Id_Sets.Set
     with Pre  => (if Fold_Functions then not Allow_Statements),
          Post => (if Reduced
                   then (for all F of Get_Variable_Set'Result
                           => F.Kind /= Record_Field));
   --  Obtain all variables used in an expression. We use Scope to
   --  determine if called subprograms should provide their abstract or
   --  refined view.
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
   --     * Allow_Statements: if False, we raise an exception if we
   --       encounter certain statements such as procedure calls.
   --
   --     * Expand_Synthesized_Constants: if True, then constants that do
   --       not come from source are expanded out to the variable set of
   --       their initializing expression.

   function Get_Variable_Set
     (L                            : List_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Allow_Statements             : Boolean := False;
      Expand_Synthesized_Constants : Boolean := False)
      return Flow_Id_Sets.Set;
   --  As above, but operating on a list. Note we don't have the
   --  Consider_Extensions parameter here as its implicitly false.

   function Quantified_Variables (N : Node_Id) return Flow_Id_Sets.Set;
   --  Return the set of entire variables which are introduced in a
   --  quantifier under node N

   function Is_Null_Record (E : Entity_Id) return Boolean
     with Pre => Nkind (E) in N_Entity;
   --  Checks if E is a record that contains no fields at all. If E is not
   --  a record we return False.

   function Flatten_Variable
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Flow_Id_Sets.Set
     with Pre => F.Kind in Direct_Mapping |
                           Record_Field |
                           Magic_String |
                           Synthetic_Null_Export;
   --  The idea is to take a flow id F and split it up into all relevant
   --  parts. For example, we might take X.Y and produce X.Y.A and X.Y.B,
   --  or just X.Y (if we can't se the private part of X.Y's type).
   --
   --  For magic strings and the null export, we simply return a set
   --  containing just that.
   --
   --  Note in cases where we are dealing with a null record this function
   --  returns the empty set, but in general you can expect at least one
   --  element in the result.
   --
   --  For private types we just return F. For private types with
   --  discriminant C we return F.C and F'Hidden.
   --
   --  For tagged types T we just return all components as usual. For
   --  classwide types we also return T'Extension and T'Tag.

   function Flatten_Variable
     (E     : Entity_Id;
      Scope : Flow_Scope)
      return Flow_Id_Sets.Set
   is (Flatten_Variable (Direct_Mapping_Id (Unique_Entity (E)), Scope))
     with Pre  => Nkind (E) in N_Entity,
          Post => (if not Is_Null_Record (E)
                   then not Flatten_Variable'Result.Is_Empty);
   --  As above, but conveniently taking an Entity instead of a Flow_Id.

   subtype Valid_Assignment_Kinds is Node_Kind with Static_Predicate =>
     Valid_Assignment_Kinds in N_Identifier                |
                               N_Expanded_Name             |
                               N_Type_Conversion           |
                               N_Unchecked_Type_Conversion |
                               N_Indexed_Component         |
                               N_Slice                     |
                               N_Selected_Component;

   function Is_Valid_Assignment_Target (N : Node_Id) return Boolean
     with Post => (if Is_Valid_Assignment_Target'Result
                   then Nkind (N) in Valid_Assignment_Kinds);
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
          Post =>
            Map_Root.Kind in Direct_Mapping | Record_Field and then
            (for all X of Seq => Nkind (X) in Valid_Assignment_Kinds);
   --  Checks the assignment target N and determines a few basic
   --  properties.
   --
   --  * Partial_Definition: if set this indicates that the assignment to N
   --    touches only a few elements of a larger array.
   --  * View_Conversion: indicates that N contains a view conversion.
   --  * Classwide: the assignment to map_root is classwide.
   --  * Map_Root: the non-flattened flow_id which is assigned to.
   --  * Seq: the list of items used to derive Map_Root.

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
          Post => (if not Is_Null_Record (Etype (N))
                   then not Vars_Defined.Is_Empty);
   --  Process the LHS of an assignment statement or an [in] out parameter,
   --  establising the sets of variables used. For example, assume we have
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
   --  general and thus will be processed by Get_Variable_Set.
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
     with Pre => Ekind (Get_Full_Type (N, Scope)) in Record_Kind | Private_Kind
                 and then Map_Root.Kind in Direct_Mapping | Record_Field
                 and then Nkind (Map_Type) in N_Entity
                 and then Ekind (Map_Type) in Type_Kind;
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
   --  Expand_Synthesized_Constants will be passed on to Get_Variable_Set
   --  if necessary.
   --
   --  Get_Variable_Set will be called with Reduced set to False (as this
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
                 or else Is_Tick_Update (N);
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
   --  Expand_Synthesized_Constants will be passed on to Get_Variable_Set
   --  if necessary.
   --
   --  Get_Variable_Set will be called with Reduced set to False (as this
   --  function should never be called when its true...)

   function Get_Precondition_Expressions (E : Entity_Id) return Node_Lists.List
     with Pre => Ekind (E) in Subprogram_Kind;
   --  Given the entity for a subprogram, return the expression(s) for
   --  its precondition and the condition(s) of its Contract_Cases (or
   --  return the empty list if none of these exist).

   function Get_Postcondition_Expressions (E       : Entity_Id;
                                           Refined : Boolean)
                                           return Node_Lists.List
     with Pre => Ekind (E) in Subprogram_Kind | E_Package;
   --  Given the entity for a subprogram or package, return all
   --  expression(s) associated with postconditions: the
   --  postcondition, the rhs for contract cases and the initial
   --  condition; or an empty list of none of these exist.

   function Is_Precondition_Check (N : Node_Id) return Boolean
     with Pre => Nkind (N) = N_Pragma and then
                 Get_Pragma_Id (N) = Pragma_Check;
   --  Given a check pragma, return if this is a precondition check.

   function Contains_Discriminants
     (F : Flow_Id;
      S : Flow_Scope)
      return Boolean
     with Pre => F.Kind in Direct_Mapping | Magic_String;
   --  Returns true if the flattened variable for F contains at least
   --  one discriminant.

   function Is_Initialized_At_Elaboration (F : Flow_Id;
                                           S : Flow_Scope)
                                           return Boolean;
   --  Returns true if F is covered by an initializes aspect. If F is not a
   --  record or direct mapping, we return false. (A magic string by
   --  definition cannot be mentioned in an initializes aspect.)
   --
   --  This mirrors Is_Initialized_At_Elaboration from Flow_Tree_Utility,
   --  but works for a Flow_Id instead of an Entity_Id.

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

   procedure Add_Loop_Write (E : Entity_Id;
                             F : Flow_Id)
     with Pre => Ekind (E) = E_Loop;
   --  Adds F to the set of variables written by the loop E.

   procedure Freeze_Loop_Info;
   --  Must be called at the end of flow analysis - this makes it an error
   --  to use Add_Loop and Add_Loop_Write, and enables the use of
   --  Get_Loop_Writes.

   function Loop_Writes_Known (E : Entity_Id) return Boolean
     with Pre => Ekind (E) = E_Loop;
   --  Checks if the variables written by loop E are known.

   function Get_Loop_Writes (E : Entity_Id) return Flow_Id_Sets.Set
     with Pre => Ekind (E) = E_Loop and then
                 Loop_Writes_Known (E);
   --  Returns the set of variables a given loop *may* write to. Please
   --  note that if a function returns inside a loop, the name of the
   --  function will be "written to" and will be returned here.

   function Get_Type (F     : Flow_Id;
                      Scope : Flow_Scope)
                      return Entity_Id
     with Pre  => F.Kind in Direct_Mapping | Record_Field and then
                  F.Facet = Normal_Part,
          Post => Nkind (Get_Type'Result) in N_Entity;
   --  Determine the type of a flow_id.

   function Extensions_Visible (E     : Entity_Id;
                                Scope : Flow_Scope)
                                return Boolean
     with Pre => Ekind (E) in Object_Kind | E_Function | E_Abstract_State;
   --  Checks if extensions are visible for this particular entity. Note
   --  that if we give it a function, then we always return false, since
   --  this refers to the return of the function, not if the subprogram's
   --  aspect.
   --
   --  To check if a subprogram has the aspect, use the function
   --  Has_Extensions_Visible_Aspect from Flow_Tree_Utilities instead.

   function Extensions_Visible (F     : Flow_Id;
                                Scope : Flow_Scope)
                                return Boolean
     with Pre => (if F.Kind in Direct_Mapping | Record_Field
                  then Ekind (Get_Direct_Mapping_Id (F))
                    in Object_Kind | E_Function | E_Abstract_State);
   --  As above, but using a flow_id.

   function Search_Depends (Subprogram : Entity_Id;
                            Output     : Entity_Id;
                            Input      : Entity_Id := Empty)
                            return Node_Id
     with Pre  => Nkind (Subprogram) in N_Entity and then
                  Ekind (Subprogram) in Subprogram_Kind and then
                  Nkind (Output) in N_Entity and then
                  (if Present (Input) then Nkind (Input) in N_Entity),
          Post => Present (Search_Depends'Result);
   --  Search the depends (or refined depends) of the given subprogram for
   --  the given output. If input is also given, search for that input in
   --  the dependency list for the given output.
   --
   --  If we can't find what we're looking for, we return the subprogram
   --  itself.

   function All_Components (E : Entity_Id) return Node_Lists.List
     with Pre => Nkind (E) in N_Entity and then
                 Ekind (E) in Type_Kind;
   --  Obtain all components of the given entity E, similar to
   --  {First,Next}_Component_Or_Discriminant, with the difference that any
   --  components of private ancestors are included.

   function Is_Non_Visible_Constituent
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Boolean;
   --  Returns True if F is not visible from Scope and is a
   --  constituent of some state abstraction. This means that F will
   --  have to be up projected.

   function Up_Project_Constituent
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Flow_Id
     with Pre => Is_Non_Visible_Constituent (F, Scope);
   --  Returns the Flow_Id of the closest enclosing state of F that
   --  Is_Visible from Scope.

end Flow_Utility;
