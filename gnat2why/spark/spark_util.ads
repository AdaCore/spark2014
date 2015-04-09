------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            S P A R K _ U T I L                           --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                        Copyright (C) 2012-2015, AdaCore                  --
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

with AA_Util;               use AA_Util;
with Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Atree;                 use Atree;
with Common_Containers;     use Common_Containers;
with Einfo;                 use Einfo;
with Impunit;               use Impunit;
with Lib;                   use Lib;
with Namet;                 use Namet;
with Sem_Util;              use Sem_Util;
with Sinfo;                 use Sinfo;
with Sinput;                use Sinput;
with Snames;                use Snames;
with Types;                 use Types;
with Uintp;                 use Uintp;
with Why.Atree.Tables;      use Why.Atree.Tables;

package SPARK_Util is

   ----------------------------------------------------------------------
   --  Utility types related to entities and nodes
   ----------------------------------------------------------------------

   subtype Subtype_Kind is Entity_Kind with
     Static_Predicate => Subtype_Kind in E_Enumeration_Subtype
                                       | E_Signed_Integer_Subtype
                                       | E_Modular_Integer_Subtype
                                       | E_Ordinary_Fixed_Point_Subtype
                                       | E_Decimal_Fixed_Point_Subtype
                                       | E_Floating_Point_Subtype
                                       | E_Access_Subtype
                                       | E_Array_Subtype
                                       | E_String_Subtype
                                       | E_String_Literal_Subtype
                                       | E_Class_Wide_Subtype
                                       | E_Record_Subtype
                                       | E_Record_Subtype_With_Private
                                       | E_Private_Subtype
                                       | E_Limited_Private_Subtype
                                       | E_Incomplete_Subtype
                                       | E_Protected_Subtype
                                       | E_Task_Subtype;

   use type Ada.Containers.Count_Type;

   function Lexicographic_Entity_Order
     (Left, Right : Entity_Id) return Boolean;
   --  Ordering for entities based on their unique name. Returns true
   --  if Left is considered to be "less than" Right.

   package Unbounded_String_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Unbounded_String);

   ---------------------------------
   -- Queries related to entities --
   ---------------------------------

   function Get_Return_Object_Entity (Stmt : Node_Id) return Entity_Id
     with Pre => Nkind (Stmt) = N_Extended_Return_Statement;
   --  @param Stmt an extended return statement
   --  @return the corresponding return object

   procedure Add_Full_And_Partial_View (Full, Partial : Entity_Id);
   --  Store the correspondance between the Full and Partial views of the same
   --  entity, for deferred constants and private types.

   function Is_Full_View (E : Entity_Id) return Boolean;
   --  Return whether E is the full view of another entity

   function Is_Partial_View (E : Entity_Id) return Boolean;
   --  Return whether E is the partial view of another entity

   function Entity_In_External_Axioms (E : Entity_Id) return Boolean;
   --  Return whether an entity E is declared in a package with external axioms

   function Partial_View (E : Entity_Id) return Entity_Id;
   --  Return the partial view for entity E

   function Full_Name (N : Entity_Id) return String
     with Pre => (Nkind (N) in N_Entity);
   --  @param N an entity
   --  @return its full name, as used in Why

   function Full_Name_Is_Not_Unique_Name (N : Entity_Id) return Boolean;
   --  The full name of an entity is based on its unique name in nearly all
   --  cases, so that this name can be used e.g. to retrieve completion
   --  theories. In a few cases which require special handling
   --  (currently Standard_Boolean and Universal_Fixed), the full name is hard
   --  coded for Why, so should not be used as a representative of the entity.
   --  @param N an entity
   --  @return True iff the Full Name as computed by Full_Name does not
   --    correspond to the type name used in Why

   function Source_Name (E : Entity_Id) return String;
   --  @param E an entity
   --  @return the unscoped name of the entity as it appears in the source

   function Is_Toplevel_Entity (E : Entity_Id) return Boolean;
   --  Returns True if E is a toplevel entity, only enclosed in package specs
   --  or in the declaration part of package bodies.

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean
     with Pre => (Ekind (E) = E_Loop_Parameter);
   --  @param E an entity with kind Loop_Parameter
   --  @return True iff E has been introduced by a quantified expression

   function Analysis_Requested (E : Entity_Id) return Boolean;
   --  Returns true if entity E has to be analyzed.

   function Is_In_Analyzed_Files (E : Entity_Id) return Boolean;
   --  Returns true if E belongs to one of the entities that correspond
   --  to the files that are to be analyzed.

   function Is_Package_State (E : Entity_Id) return Boolean;
   --  Returns True if E is declared in a package spec or body. Also
   --  returns True for any abstract state.

   function Has_Volatile (E : Entity_Id) return Boolean
     with Pre => Nkind (E) in N_Entity;
   --  Checks if the given entity is volatile.

   function Has_Volatile_Aspect (E : Entity_Id;
                                 A : Pragma_Id)
                                 return Boolean
     with Pre => Has_Volatile (E) and
                 A in Pragma_Async_Readers    | Pragma_Async_Writers |
                      Pragma_Effective_Writes | Pragma_Effective_Reads;
   --  Checks if the given entity (or its type) has the specified aspect.

   --------------------------------------
   -- Queries related to Type Entities --
   --------------------------------------

   function MUT (T : Entity_Id) return Entity_Id with
     Pre => Ekind (T) in Type_Kind;
   --  Returns the "most underlying type" of a type T, following the chain of
   --  underlying types for private types, up to a non-private type. If T is
   --  not private, it simply returns it. E. As a special case, return the
   --  first type in a package with external axioms found.

   function MUT_Kind (T : Entity_Id) return Entity_Kind with
     Pre => Ekind (T) in Type_Kind;
   --  Returns the entity kind of the "most underlying type" of a type T.
   --  This is not the same as Ekind (MUT (T)), because MUT (T) may still
   --  be a private type for those types defined in a unit with an external
   --  axiomatization.

   --  The following functions provide wrappers for the query functions
   --  in Einfo, that apply the query on the most underlying type of its
   --  argument, hence skipping all layers of pivate types. To avoid confusion,
   --  the wrapper for function Einfo.Is_Such_And_Such_Type is called
   --  Has_Such_And_Such_Type.

   function Has_Access_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Access_Kind);

   function Has_Array_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Array_Kind);

   function Has_Composite_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Composite_Kind);

   function Has_Discrete_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Discrete_Kind);

   function Has_Enumeration_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Enumeration_Kind);

   function Has_Modular_Integer_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Modular_Integer_Kind);

   function Has_Record_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Record_Kind);

   function Has_Scalar_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Scalar_Kind);

   function Has_Signed_Integer_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Signed_Integer_Kind);

   function Has_Fixed_Point_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Fixed_Point_Kind);

   function Has_Floating_Point_Type (T : Entity_Id) return Boolean is
     (MUT_Kind (T) in Float_Kind);

   function Has_Static_Scalar_Subtype (T : Entity_Id) return Boolean;
   --  Returns whether type T has a scalar subtype with statically known
   --  bounds. This included looking past private types.

   function Is_Null_Range (T : Entity_Id) return Boolean;
   --  @param T a type entity
   --  @returns True iff T is a scalar type whose range is statically know to
   --     be empty

   --  The following type lists all possible forms of default initialization
   --  that may apply to a type.

   type Default_Initialization_Kind is
     (No_Possible_Initialization,
      --  This value signifies that a type cannot possibly be initialized
      --  because it has no content, for example - a null record.

      Full_Default_Initialization,
      --  This value covers the following combinations of types and content:
      --    * Access type
      --    * Array-of-scalars with specified Default_Component_Value
      --    * Array type with fully default initialized component type
      --    * Record or protected type with components that either have a
      --      default expression or their related types are fully default
      --      initialized.
      --    * Scalar type with specified Default_Value
      --    * Task type
      --    * Type extension of a type with full default initialization where
      --      the extension components are also fully default initialized.

      Mixed_Initialization,
      --  This value applies to a type where some of its internals are fully
      --  default initialized and some are not.

      No_Default_Initialization);
      --  This value reflects a type where none of its content is fully
      --  default initialized.

   function Default_Initialization
     (Typ           : Entity_Id;
      Explicit_Only : Boolean    := False)
      return Default_Initialization_Kind;
   --  Determine default initialization kind that applies to a particular
   --  type. Types defined in axiomatized units (such as formal containers) and
   --  private types are treated specially, so that they are either considered
   --  as having full default initialized, or no default initialization.
   --  @param Typ The type that for which we need to determine initialization.
   --  @param Explicit_Only If True then do not consider attributes
   --    Has_Default_Init_Cond and Has_Inherited_Default_Init_Cond for this
   --    type.
   --  @return the Default_Initialization_Kind of Typ

   function Get_Low_Bound (E : Entity_Id) return Node_Id;
   --  @param E an index subtype or string literal subtype
   --  @return its low bound

   function Has_User_Defined_Eq (E : Entity_Id) return Entity_Id
     with Pre => Ekind (E) in Type_Kind;
   --  @param E a type entity
   --  @return the entity of the primitive equality function of the type
   --    entity, if it exists; otherwise return the empty node

   procedure Add_Classwide_To_Tagged (Classwide, Ty : Entity_Id);
   --  Store the correspondance between a classwide type and the specific
   --  corresponding type.

   function Corresponding_Tagged (Classwide : Entity_Id) return Entity_Id;
   --  Returns the specific tagged type corresponding to a classwide type

   function Is_Single_Precision_Floating_Point_Type
     (E : Entity_Id) return Boolean;
   --  Return whether E is a single precision floating point type,
   --  characterized by:
   --  . machine_radix = 2
   --  . machine_mantissa = 24
   --  . machine_emax = 2**7
   --  . machine_emin = 3 - machine_emax

   function Is_Double_Precision_Floating_Point_Type
     (E : Entity_Id) return Boolean;
   --  Return whether E is a double precision floating point type,
   --  characterized by:
   --  . machine_radix = 2
   --  . machine_mantissa = 53
   --  . machine_emax = 2**10
   --  . machine_emin = 3 - machine_emax

   function Type_Based_On_External_Axioms (E : Entity_Id) return Boolean;
   --  Return whether a private type E is defined in the private part of a
   --  package with external axioms, or it is a subtype or derived type
   --  ultimately based on such a type.

   function Underlying_External_Axioms_Type (E : Entity_Id) return Entity_Id;
   --  Return the underlying (private) base type declared in a package with
   --  external axioms of a private type E, if any

   function Root_Record_Type (E : Entity_Id) return Entity_Id;
   --  Given a record type (or private type whose implementation is a record
   --  type, etc.), return the root type, including traversing private types.

   function Root_Record_Component (E : Entity_Id) return Entity_Id;
   --  Given a component or discriminant of a record (sub-)type, return the
   --  corresponding component or discriminant of the root type, if any. This
   --  is the identity when E is the component of a root type.

   function Search_Component_By_Name
     (Rec  : Entity_Id;
      Comp : Entity_Id) return Entity_Id;
   --  Given a record type entity and a component/discriminant entity, search
   --  in Rec a component/discriminant entity with the same name. Returns Empty
   --  if no such component is found.

   function Matching_Component_Association
     (Component   : Entity_Id;
      Association : Node_Id) return Boolean;
   --  Return whether Association matches Component

   function Number_Components (Typ : Entity_Id) return Natural;
   --  Count the number of components in an Ada record type Typ

   function Number_Discriminants (Typ : Entity_Id) return Natural;
   --  Count the number of discriminants in an Ada record type Typ

   function Count_Why_Top_Level_Fields (E : Entity_Id) return Natural;
   --  Number of elements in the complete record type. It should contain:
   --    - A field __split_discrs for discriminants if E has at list one
   --    - A field __split_fields for components if E has at list one
   --      regular field (use Count_Why_Regular_Fields)
   --    - A field attr__constrained if E's discriminants have defaults
   --    - A field __tag if E is tagged
   --  Note that tagged types have always at least one component, for the
   --  components of possible extensions.

   function Count_Why_Regular_Fields (E : Entity_Id) return Natural;
   --  Number of regular fields in a record type Typ. It includes:
   --    - A field per component of E visible in SPARK
   --     (use Component_Is_Visible_In_SPARK)
   --    - A field for the private part of E if E is a private type
   --    - A field for the extensions of E if E is tagged
   --    - A field for the private components of E's private ancestors if E is
   --      tagged and has pivate ancestors (use Has_Private_Ancestor_Or_Root)

   function Component_Is_Visible_In_SPARK (E : Entity_Id) return Boolean;
   --  Returns True on components of Records which are declared in a scope
   --  with SPARK_Mode On.

   function Has_Private_Ancestor_Or_Root (E : Entity_Id) return Boolean;
   --  Returns True on taged types with a private ancestor or a private root
   --  with fullview not in SPARK

   function Nth_Index_Type (E : Entity_Id; Dim : Positive) return Node_Id
     with Pre => Is_Array_Type (E);
   --  @param E an array type entity
   --  @param D specifies a dimension
   --  @return the argument E in the special case where E is a string literal
   --    subtype; otherwise the index type entity which corresponds to the
   --    selected dimension

   function Nth_Index_Type (E : Entity_Id; Dim : Uint) return Node_Id
     with Pre => Is_Array_Type (E);
   --  same as above, but with Uint instead of positive

   function Count_Non_Inherited_Discriminants
     (Assocs : List_Id) return Natural;
   --  Counts the number of discriminants in the list of component associations
   --  Assocs.

   function First_Discriminant (Id : E) return E
     with Pre =>
       (Is_Record_Type (Id) or else Is_Incomplete_Or_Private_Type (Id));
   --  Get the first discriminant of the record type entity [Id]. Contrary
   --  to Sem_Aux.First_Discriminant, it does not skip hidden stored
   --  discriminants.

   function Is_External_Axioms_Discriminant (E : Entity_Id) return Boolean
   with
     Pre => Ekind (E) = E_Discriminant;

   function Is_Access_To_External_Axioms_Discriminant
     (N : Node_Id) return Boolean
   with
     Pre => Nkind (N) = N_Selected_Component;

   function Get_Specific_Type_From_Classwide (E : Entity_Id) return Entity_Id
   with
     Pre => Is_Class_Wide_Type (E);
   --  Returns the specific type associated with a class wide type.
   --  If E's Etype is a fullview, returns its partial view instead.

   function Has_Default_Init_Condition (E : Entity_Id) return Boolean with
     Pre => Is_Type (E);

   function Get_Default_Init_Cond_Proc (E : Entity_Id) return Entity_Id with
     Pre => Is_Type (E) and then Has_Default_Init_Condition (E);
   --  Return the default initial condition procedure for a type E

   function Is_Standard_Boolean_Type (N : Node_Id) return Boolean;
   --  Returns True if N is a sybtype of Standard_Boolean with the same
   --  Scalar_Range

   function Is_Static_Array_Type (E : Entity_Id) return Boolean
   is (Is_Array_Type (E)
       and then Is_Constrained (E)
       and then Has_Static_Array_Bounds (E))
   with Pre => (Ekind (E) in Type_Kind);
   --  @param E a type entity
   --  @return True if the type entity corresponds to a static constrained
   --    array type

   function Static_Array_Length (E : Entity_Id; Dim : Positive) return Uint
     with Pre => Is_Static_Array_Type (E);
   --  @param E a type entity which corresponds to a static constrained array
   --    type
   --  @param Dim the selected dimension of the array type
   --  @return the static length of the selected dimension of the array type as
   --    an integer

   function Has_Static_Discrete_Predicate (E : Entity_Id) return Boolean;
   --  @param E a type entity
   --  @return True if the type is a discrete type with a static predicate

   function Get_Cursor_Type_In_Iterable_Aspect
     (Typ : Entity_Id) return Entity_Id;
   --  Returns the cursor type implied by an Iterable aspect over the type Typ

   function Get_Element_Type_In_Iterable_Aspect
     (Typ : Entity_Id) return Entity_Id;
   --  Returns the element type implied by an Iterable aspect over the type Typ

   function Get_Default_Init_Cond_Pragma (Typ : Entity_Id) return Node_Id with
     Pre => Has_Default_Init_Cond (Typ) or else
            Has_Inherited_Default_Init_Cond (Typ);
   --  Returns the unanalyzed pragma Default_Initial_Condition applying to a
   --  type.

   function Check_Needed_On_Conversion (From, To : Entity_Id) return Boolean;
   --  Returns whether a check may be needed when converting an expression
   --  of type From to an expression of type To. Currently a very coarse
   --  approximation to rule out obvious cases.

   function Get_Full_Type_Without_Checking (N : Node_Id) return Entity_Id
     with Pre => Present (N);
   --  Get the type of the given entity. This function looks through
   --  private types and should be used with extreme care.

   -----------------------------------
   -- Queries Related to Subprogams --
   -----------------------------------

   function Find_Contracts
     (E         : Entity_Id;
      Name      : Name_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Node_Lists.List
   with
     Pre => Ekind (E) in Subprogram_Kind | E_Package and then
             not (Classwide and Inherited);
   --  Walk the Contract node attached to E and return the pragma matching
   --  Name.

   function Has_Contracts
     (E         : Entity_Id;
      Name      : Name_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Boolean
   with Pre => Ekind (E) in Subprogram_Kind | E_Package;
   --  Return True if the subprogram in argument has the given kind of
   --  contract, False otherwise.

   function Get_Expression_Function (E : Entity_Id) return Node_Id;
   --  If E is the entity of an expression function, return the corresponding
   --  N_Expression_Function original node. Otherwise, return Empty.

   function Get_Subprogram_Body (E : Entity_Id) return Node_Id;
   --  Return the N_Subprogram_Body node for a subprogram entity E, if
   --  available. Otherwise, return Empty.

   function Get_Subprogram_Spec (E : Entity_Id) return Node_Id;
   --  Return the N_Specification node for a subprogram entity E

   function Get_Subprogram_Decl (E : Entity_Id) return Node_Id;
   --  Return the N_Subprogram_Declaration node for a subprogram entity E, if
   --  any. Otherwise, return Empty, in particular in the case of a subprogram
   --  body acting as declaration.

   function Get_Subprogram_Contract_Cases (E : Entity_Id) return Node_Id;
   --  Return the pragma Contract_Cases for E, if any

   function Expression_Functions_All_The_Way (E : Entity_Id) return Boolean;
   --  Given the entity E for a function, determine whether E is an expression
   --  function that only calls expression functions, directly or indirectly.

   function Is_Overriding_Subprogram (E : Entity_Id) return Boolean;
   --  Returns True if E is an overriding subprogram

   function Is_Simple_Shift_Or_Rotate (E : Entity_Id) return Boolean;
   --  @param E Subprogram entity.
   --  @return True iff Subp is an intrisic shift or rotate for a modular type
   --     of modulus smaller or equal to 2 ** 64, with no functional contract
   --     (precondition, postcondition or contract cases).

   function Is_Unchecked_Conversion_Instance (E : Entity_Id) return Boolean;
   --  Returns whether E is an instance of Ada.Unchecked_Conversion

   function Subprogram_Full_Source_Name (E : Entity_Id) return String;
   --  For a subprogram entity, return its scoped name, e.g. for subprogram
   --  Nested in
   --
   --    package body P is
   --       procedure Lib_Level is
   --          procedure Nested is
   --     ....
   --  return P.Lib_Level.Nested. Casing of names is taken as it appears in the
   --  source.
   --  @param E a subprogram entity
   --  @return it's fully scoped name as it appears in the source

   function Subp_Location (E : Entity_Id) return String
     with Pre => (Ekind (E) in Subprogram_Kind | E_Package);
   --  @param E a subprogram or package entity
   --  @return a string of the form GP_Subp:foo.ads:12, where this is the file
   --    and line where this subprogram or package is declared. Tihs allows to
   --    identify the subprogram by it's source position and is used e.g. for
   --    the --limit-subp opion of gnatprove.

   type Execution_Kind_T is (Normal_Execution,
                             Abnormal_Termination,
                             Infinite_Loop);
   --  Please be *exceptionally* alert when adding elements to this type,
   --  as many checks simlpy check for one of the options (and do not
   --  explicitly make sure all cases are considered).

   function Get_Abend_Kind
     (E          : Entity_Id;
      GG_Allowed : Boolean := True) return Execution_Kind_T;
   --  Infer how the Called_Procedure abnormally ends. If a subprogram
   --  has an output, we assume that it contains an infinite loop. If it
   --  does not, we assume its a thinly veiled wrapper around an
   --  exception raising program.
   --
   --  Certainly, if you have a procedure that never returns due to an
   --  exception, and it is implemented in SPARK, then you will run into
   --  trouble unless there is nothing of interest going on in it.
   --
   --  If we get this wrong, its not the end of the world, as failure is
   --  safe:
   --
   --  A) If the procedure throws an exception, but we think it loops
   --     forever (because it has outputs), then you might get *extra*
   --     data dependencies.
   --
   --  B) If the procedure loops forever, and:
   --     i) it has no outputs, its indistinguishable from an exception
   --     ii) it has outputs we classify it correctly
   --
   --  C) If the procedure loops forever but is not in SPARK and we have
   --     lied about contracts (as in, stated it has no outputs), then
   --     this is not a "new" failure.

   function Has_No_Output
     (E          : Entity_Id;
      GG_Allowed : Boolean) return Boolean
   with
     Pre => Nkind (E) in N_Entity and then Ekind (E) = E_Procedure;
   --  Returns True if procedure E has no output (parameter or global).
   --  Otherwise, or if we don't know for sure, we return False.
   --
   --  If GG_Allowed is False, then we will not query generated globals. This
   --  is useful before generated globals are computed.

   function Has_User_Supplied_Globals (E : Entity_Id) return Boolean
     with Pre => Nkind (E) in N_Entity and then Ekind (E) in Subprogram_Kind;
   --  Return true if the given subprogram has been annotated with a global
   --  (or depends) contract.

   function Subprogram_Is_Ignored_For_Proof (E : Entity_Id) return Boolean with
     Pre => Ekind (E) in E_Procedure | E_Function;
   --  Returns true on subprograms that are not translated to Why.

   function Is_Requested_Subprogram (E : Entity_Id) return Boolean;
   --  Returns true if entity E is the one whose analysis was specifically
   --  requested, so it should be analyzed even if otherwise inlined.

   function Is_Local_Subprogram_Always_Inlined (E : Entity_Id) return Boolean;
   --  Returns True if E is a local subprogram that is always inlined by the
   --  frontend in GNATprove mode.

   function Get_Expr_From_Check_Only_Proc (E : Entity_Id) return Node_Id with
     Pre => Ekind (E) = E_Procedure;
   --  Goes through a subprogram containing only a pragma Check (Expr) and
   --  returns Expr. Returns Empty if there is no such pragma.

   function Get_Procedure_Specification (E : Entity_Id) return Node_Id
     with Pre  => Ekind (E) = E_Procedure,
          Post => Nkind (Get_Procedure_Specification'Result) =
                    N_Procedure_Specification;

   function Might_Be_Main (E : Entity_Id) return Boolean
     with Pre => Ekind (E) in Subprogram_Kind;
   --  Returns True if E is a library level subprogram without formal
   --  parameters (E is allowed to have global parameters).

   ---------------------------------
   -- Queries Related to Packages --
   ---------------------------------

   function Get_Package_Spec (E : Entity_Id) return Node_Id with
     Pre  => Ekind_In (E, E_Package, E_Generic_Package),
     Post => Nkind (Get_Package_Spec'Result) = N_Package_Specification;
   --  Return the specification node for a package entity E

   function Get_Package_Decl (E : Entity_Id) return Node_Id with
     Pre  => Ekind_In (E, E_Package, E_Generic_Package),
     Post => Nkind_In (Get_Package_Decl'Result,
                       N_Package_Declaration,
                       N_Generic_Package_Declaration);
   --  Return the declaration node for a package entity E

   function Get_Package_Body (E : Entity_Id) return Node_Id with
     Pre  => Ekind_In (E, E_Package, E_Generic_Package),
     Post => (if Present (Get_Package_Body'Result) then
                Nkind (Get_Package_Body'Result) = N_Package_Body);
   --  Return the declaration node for the body of a package entity E, if there
   --  is one.

   function In_Private_Declarations (Decl : Node_Id) return Boolean;
   --  Returns whether Decl belongs to the list of private declarations of a
   --  package.

   function Package_Has_External_Axioms (E : Entity_Id) return Boolean with
     Pre  => Ekind_In (E, E_Package, E_Generic_Package);
   --  Return whether E is a package with External Axioms

   function Has_Extensions_Visible_Aspect (E : Entity_Id) return Boolean
     with Pre => Nkind (E) in N_Entity and then
                 Ekind (E) in Subprogram_Kind;
   --  Checks if extensions are visible for this subprogram.

   -------------------------------
   --  Queries for Pragma Nodes --
   -------------------------------

   function Is_Pragma (N : Node_Id; Name : Pragma_Id) return Boolean;
   --  Returns whether N is a pragma of the given kind

   function Is_Pragma_Annotate_Gnatprove (N : Node_Id) return Boolean;
   --  Returns True if N has the form pragma Annotate (Gnatprove,...);

   function Is_Pragma_Check (N : Node_Id; Name : Name_Id) return Boolean;
   --  Returns whether N has the form pragma Check (Name, ...)

   function Is_Ignored_Pragma_Check (N : Node_Id) return Boolean;
   --  Returns whether N is a pragma check that can be ignored by analysis,
   --  because it is already taken into account elsewhere (precondition and
   --  postcondition, static predicate), or because it is completely ignored
   --  with a warning in SPARK.Definition (dynamic predicate).

   function Is_Pragma_Assert_And_Cut (N : Node_Id) return Boolean
     with Pre => (Nkind (N) = N_Pragma);
   --  @param N a pragma Node
   --  @return True iff the pragma is a pragma Assert_And_Cut

   procedure Get_Global_Items
     (P      : Node_Id;
      Reads  : out Node_Sets.Set;
      Writes : out Node_Sets.Set);
   --  Returns the set of input and output items in Global pragma P

   function Get_Body_Entity (E : Entity_Id) return Entity_Id
     with Pre  => Ekind (E) in E_Function | E_Procedure,
          Post => (not Present (Get_Body_Entity'Result))
                    or else Ekind (Get_Body_Entity'Result) = E_Subprogram_Body;
   --  Fetches the body entity for a subprogram with a spec and a body.

   ---------------------------------
   -- Queries for Arbitrary Nodes --
   ---------------------------------

   function Get_Enclosing_Declaration (N : Node_Id) return Node_Id;
   --  Return the declaration node enclosing N, if any, by following the chain
   --  of Parent's links.

   function Get_Enclosing_Unit (E : Entity_Id) return Entity_Id;
   --  Return the entity of the package or subprogram enclosing E.

   function Is_Declared_In_Unit (E : Entity_Id; Scope : Entity_Id)
                                 return Boolean;
   --  Returns True if E is declared directly in Scope.

   function Spec_File_Name_Without_Suffix (N : Node_Id) return String;
   --  @param any node
   --  @return same as Spec_File_Name but without the suffix.

   function String_Of_Node (N : Node_Id) return String;
   --  @param any expression node
   --  @return the node as pretty printed Ada code, limited to 50 chars

   function In_Main_Unit_Body (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is in the body of the currently analyzed unit

   function In_Main_Unit_Spec (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is in the spec of the currently analyzed unit

   function Is_In_Current_Unit (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is in the body or spec of the currently analyzed unit

   function Spec_File_Name (N : Node_Id) return String;
   --  @param N any node
   --  @return the name of the spec file of the unit which contains the node,
   --    if it exists, otherwise the body file. Also, we return the file name
   --    of the instance, not the generic.

   function Body_File_Name (N : Node_Id) return String;
   --  @param N any node
   --  @return Same as [Spec_File_Name], but always return the file name of the
   --    body, if there is one.

   function Innermost_Enclosing_Loop (N : Node_Id) return Node_Id;
   --  Returns the innermost loop enclosing N

   function Get_Enclosing (N : Node_Id; K : Node_Kind) return Node_Id
     with Post => Nkind (Get_Enclosing'Result) = K;
   --  Returns the first parent P of N where Nkind (P) = K.

   ----------------------------------
   -- Queries for Particular Nodes --
   ----------------------------------

   function Get_Range (N : Node_Id) return Node_Id
      with Post =>
         (Present (Low_Bound (Get_Range'Result)) and then
            Present (High_Bound (Get_Range'Result)));
   --  @param N more or less any node which has some kind of range, e.g. a
   --  scalar type entity or occurrence, a variable of such type, the type
   --  declaration or a subtype indication.
   --  @return the N_Range node of such a node
   --  @exception Program_Error if N is not of appropriate kind (doesn't have a
   --  range)

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean;
   --  Return whether aggregate or an extension aggregate N is fully
   --  initialized. For the aggregate extension, this only deals with
   --  the extension components.

   function All_Aggregates_Are_Fully_Initialized
     (N : Node_Id) return Boolean;
   --  Return whether all aggregates in node N (recursively) are fully
   --  initialized.

   function Is_Predicate_Function_Call (N : Node_Id) return Boolean;
   --  Returns whether N is a call to a frontend-generated predicate function

   function Get_Formal_From_Actual (Actual : Node_Id) return Entity_Id
   with
     Pre => Nkind_In (Parent (Actual), N_Function_Call,
                                       N_Parameter_Association,
                                       N_Procedure_Call_Statement);
   --  Given an actual parameter Actual of a call, returns the type of the
   --  corresponding formal parameter.

   generic
      with procedure Handle_Argument (Formal, Actual : Node_Id);
   procedure Iterate_Call_Arguments (Call : Node_Id);
   --  Call "Handle_Argument" for each pair Formal/Actual of a function or
   --  procedure call.
   --  @param Call a node which corresponds to a function or procedure call. It
   --    must have a "Name" field and a "Parameter_Associations" field.

   function Is_Tick_Update (N : Node_Id) return Boolean
   is (Nkind (N) = N_Attribute_Reference  and then
         Get_Attribute_Id (Attribute_Name (N)) = Attribute_Update);
   --  Checks if the given node is a 'Update node.

   ------------------
   -- Misc queries --
   ------------------

   function Lowercase_Has_Element_Name return String;
   --  Return the name of the function Has_Element in formal containers

   function Lowercase_Iterate_Name return String;
   --  Return the name of the function Iterate in formal containers

   function Lowercase_Capacity_Name return String;
   --  Return the name of the discriminant Capacity in formal containers

   function Unit_In_Standard_Library (U : Unit_Number_Type) return Boolean is
      (Get_Kind_Of_Unit (U) /= Not_Predefined_Unit);
   --  Returns True is unit U is in the standard library, which includes all
   --  units defined in Ada RM, and all units predefined by GNAT.

   function Location_In_Standard_Library (Loc : Source_Ptr) return Boolean;
   --  Returns True if location Loc is in a unit of the standard library, as
   --  computed by Unit_In_Standard_Library.

   procedure Append
     (To    : in out Node_Lists.List;
      Elmts : Node_Lists.List);
   --  Append all elements from list Elmts to the list To

   procedure Append
     (To    : in out Why_Node_Lists.List;
      Elmts : Why_Node_Lists.List);
   --  Append all elements from list Elmts to the list To

   function Get_Statement_And_Declaration_List
     (Stmts : List_Id) return Node_Lists.List;
   --  Given a list of statements and declarations Stmts, returns the same list
   --  seen as a container list of nodes.

   function Get_Flat_Statement_And_Declaration_List
     (Stmts : List_Id) return Node_Lists.List;
   --  Given a list of statements and declarations Stmts, returns the flattened
   --  list that includes these statements and declarations, and recursively
   --  all inner declarations and statements that appear in block statements.

   function Is_Others_Choice (Choices : List_Id) return Boolean;
   --  Returns True if Choices is the singleton list with an "others" element

   function Unit_Name return String is
     (File_Name_Without_Suffix
        (Get_Name_String (Unit_File_Name (Main_Unit))));

   function File_Name (Loc : Source_Ptr) return String is
     (Get_Name_String (File_Name
                       (Get_Source_File_Index (Loc))));
   --  @param Loc any source pointer
   --  @return the file name of the source pointer (will return the file of the
   --    generic in case of instances)

   function Translate_Location (Loc : Source_Ptr) return Source_Ptr is
     (if Instantiation_Location (Loc) /= No_Location then
           Instantiation_Location (Loc)
      else
         Loc);
   --  ??? What is this function used for? It's strange to go only one level up
   --  @param Loc any source pointer
   --  @return if the source location has been instantiated, return the
   --    instance location, otherwise Loc itself

end SPARK_Util;
