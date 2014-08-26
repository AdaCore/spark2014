------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2013-2014, Altran UK Limited                 --
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

with Flow_Types;           use Flow_Types;
with Flow_Refinement;      use Flow_Refinement;
with Flow_Dependency_Maps; use Flow_Dependency_Maps;

use type Ada.Containers.Count_Type;

package Flow_Utility is

   function Get_Flow_Id
     (Name : Entity_Name;
      View : Parameter_Variant)
      return Flow_Id;
   --  Return a suitable flow id for the unique_name of an entity. We
   --  try our best to get a direct mapping, resorting to the magic
   --  string only as a last resort.

   function Get_Full_Type_Without_Checking (N : Node_Id) return Entity_Id
     with Pre => Present (N);
   --  Get the type of the given entity. This function looks through
   --  private types and should be used with extreme care.

   function Get_Full_Type
     (N     : Node_Id;
      Scope : Flow_Scope)
      return Entity_Id
   with Pre => Present (N);
   --  Get the type of the given entity. If the full view of the type
   --  is not visible from Scope, then we return the non-full view.

   function All_Record_Components
     (Entire_Var : Entity_Id;
      Scope      : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre =>
     Ekind (Get_Full_Type_Without_Checking (Entire_Var)) in
       E_Record_Type | E_Record_Subtype | E_Class_Wide_Type;
   --  Given the record Entire_Var, return a set with all components.
   --  So, for example we might return:
   --     * p.x
   --     * p.r.a
   --     * p.r.b
   --
   --  We return components relatively to Scope. If there are
   --  discriminants that are visible from Scope then we return those
   --  discriminants too.

   function All_Record_Components
     (The_Record_Field : Flow_Id;
      Scope            : Flow_Scope)
      return Flow_Id_Sets.Set
   with Pre =>
     The_Record_Field.Kind in Direct_Mapping | Record_Field
     and then Ekind (Get_Full_Type_Without_Checking
                       (Get_Direct_Mapping_Id
                          (The_Record_Field))) in
       E_Record_Type | E_Record_Subtype | E_Class_Wide_Type;
   --  As above but only include fields that are equal to Record_Field or are
   --  nested under it. For example if Record_Field = p.r for the above
   --  record, then we will get the following set:
   --     * p.r.a
   --     * p.r.b

   function Has_User_Supplied_Globals (Subprogram : Entity_Id) return Boolean
     with Pre => Ekind (Subprogram) in Subprogram_Kind;
   --  Return true if the given subprogram has been annotated with a global
   --  (or depends) contract.

   function Has_Depends (Subprogram : Entity_Id) return Boolean
     with Pre => Ekind (Subprogram) in Subprogram_Kind;
   --  Return true if the given subprogram has been annotated with a
   --  dependency relation.

   procedure Get_Depends (Subprogram : Entity_Id;
                          Scope      : Flow_Scope;
                          Depends    : out Dependency_Maps.Map)
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
   --  This procedure can deal with all forms the depends
   --  annotation. For each item in the dependency annotation, the LHS
   --  and RHS can be any of the following:
   --     * (x, y, z)     (an aggregate)
   --     * x             (a variable)
   --     * null          (keyword null)
   --  One final form which is supported is the null dependency.
   --
   --  The + shorthand to mean "itself" is expanded away by the
   --  front-end and this procedure does not have to deal with it.

   procedure Get_Globals (Subprogram             : Entity_Id;
                          Scope                  : Flow_Scope;
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

   procedure Get_Proof_Globals (Subprogram : Entity_Id;
                                Reads      : out Flow_Id_Sets.Set;
                                Writes     : out Flow_Id_Sets.Set)
     with Pre  => Ekind (Subprogram) in E_Procedure | E_Function,
          Post => (for all G of Reads  => G.Variant = In_View) and
                  (for all G of Writes => G.Variant = Out_View);
   --  Same as above but Reads consists of both the Reads and Proof_Ins,
   --  discriminants receive no special handling and globals are proof
   --  globals, and we always return the most refined view possible.

   function Has_Proof_Global_Reads (Subprogram : Entity_Id) return Boolean
     with Pre => Ekind (Subprogram) in E_Procedure | E_Function;
   --  Returns True if Subprogram has a Global Input or In_Out contract,
   --  whether user-defined or generated.

   function Has_Proof_Global_Writes (Subprogram : Entity_Id) return Boolean
     with Pre => Ekind (Subprogram) in E_Procedure | E_Function;
   --  Returns True if Subprogram has a Global Output or In_Out contract,
   --  whether user-defined or generated.

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
      Expand_Synthesized_Constants : Boolean := False)
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
   --  As above, but operating on a list.

   function Quantified_Variables (N : Node_Id) return Flow_Id_Sets.Set;
   --  Return the set of entire variables which are introduced in a
   --  quantifier under node N

   function Is_Null_Record (E : Entity_Id) return Boolean
   with Pre => Nkind (E) in N_Entity;
   --  Checks if E is a record that contains no fields at all. If E is not
   --  a record we return False.

   function Flatten_Variable
     (E     : Entity_Id;
      Scope : Flow_Scope)
      return Flow_Id_Sets.Set
   with Post => (if not Is_Null_Record (E)
                 then not Flatten_Variable'Result.Is_Empty);
   --  Returns a set of flow_ids for all parts of the unique entity
   --  for E. For records this includes all subcomponents, for
   --  everything else this is just the variable E.
   --
   --  Flattening happens relatively to Scope. In the case of a
   --  private record with visible discriminants we return Flow_Ids
   --  for all discriminants and 'Hidden for the private part.

   function Flatten_Variable
     (F     : Flow_Id;
      Scope : Flow_Scope)
      return Flow_Id_Sets.Set
     with Pre => F.Kind in Direct_Mapping |
                           Magic_String |
                           Synthetic_Null_Export;
   --  As above, but for flow ids.

   procedure Untangle_Assignment_Target
     (N                    : Node_Id;
      Scope                : Flow_Scope;
      Local_Constants      : Node_Sets.Set;
      Use_Computed_Globals : Boolean;
      Vars_Defined         : in out Flow_Id_Sets.Set;
      Vars_Explicitly_Used : in out Flow_Id_Sets.Set;
      Vars_Implicitly_Used : in out Flow_Id_Sets.Set;
      Vars_Semi_Used       : in out Flow_Id_Sets.Set)
     with Pre => Nkind (N) in N_Attribute_Reference |
                              N_Expanded_Name       |
                              N_Function_Call       |
                              N_Identifier          |
                              N_Indexed_Component   |
                              N_Selected_Component  |
                              N_Slice               |
                              N_Type_Conversion     |
                              N_Unchecked_Type_Conversion;
   --  Given the target of an assignment (perhaps the left-hand-side of an
   --  assignment statement or an out vertex in a procedure call), work out
   --  which variables are actually set and which variables are used to
   --  determine what is set (in the case of arrays).
   --
   --  Explicitly used variables are used directly. In
   --     A (X) :=
   --  We have explicitly used X. The implicitly used variables are "used"
   --  variables due to a partial update. In the example above A is
   --  implicitly used.
   --
   --  Vars_Semi_Used indicates variables we "read" but do not influence
   --  the output and should not be included in dependencies. For example
   --  the proof ins of function Foo will appear in this set.
   --     A (Foo (X)) :=

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

end Flow_Utility;
