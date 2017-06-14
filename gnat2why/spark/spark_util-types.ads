------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      S P A R K _ U T I L - T Y P E S                     --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                        Copyright (C) 2016-2017, AdaCore                  --
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

with Sem_Type;
with Stand;     use Stand;
with Uintp;     use Uintp;

package SPARK_Util.Types is

   subtype Subtype_Kind is Entity_Kind with
     Static_Predicate => Subtype_Kind in E_Enumeration_Subtype
                                       | E_Signed_Integer_Subtype
                                       | E_Modular_Integer_Subtype
                                       | E_Ordinary_Fixed_Point_Subtype
                                       | E_Decimal_Fixed_Point_Subtype
                                       | E_Floating_Point_Subtype
                                       | E_Access_Subtype
                                       | E_Array_Subtype
                                       | E_String_Literal_Subtype
                                       | E_Class_Wide_Subtype
                                       | E_Record_Subtype
                                       | E_Record_Subtype_With_Private
                                       | E_Private_Subtype
                                       | E_Limited_Private_Subtype
                                       | E_Incomplete_Subtype
                                       | E_Protected_Subtype
                                       | E_Task_Subtype;

   ---------------------------------------------
   -- Queries related to representative types --
   ---------------------------------------------

   --  A type may be in SPARK even if its most underlying type (the one
   --  obtained by following the chain of Underlying_Type) is not in SPARK.
   --  In the simplest case, a private type may have its partial view in SPARK
   --  and its full view not in SPARK. In other cases, such a private type will
   --  be found on the chain of type derivation and subtyping from the most
   --  underlying type to the current type.

   --  Even when the most underlying type of a type T is in SPARK, we may not
   --  want to use it for translating T into Why3, when it is defined in a unit
   --  which is externally axiomatized. In such a case, we also want to stop at
   --  the first type in the chain of type derivation and subtyping that is
   --  externally axiomatized.

   --  The "Representative Type in SPARK" (Retysp for short) of a type T is
   --  the type that represents T in the translation into Why3. It is the most
   --  underlying type of T when it is in SPARK and not externally axiomatized,
   --  or the first private type on the chain of Underlying_Type links at the
   --  boundary between SPARK and non-SPARK, or the first private type on the
   --  chain of Underlying_Type links inside an externally axiomatized unit.
   --  For non-private types, Retysp is the identity.

   function Retysp (T : Entity_Id) return Entity_Id
   with Pre => Is_Type (T);
   --  @param T any type
   --  @return the "Representative Type in SPARK" of type T
   --  It should only be called on marked type entities (except for Itypes).

   function Retysp_Kind (T : Entity_Id) return Entity_Kind
   with Pre => Is_Type (T);
   --  @param T any type
   --  @return the entity kind of the "Representative Type in SPARK" of type T.

   function Base_Retysp (T : Entity_Id) return Entity_Id
   with Pre => Is_Type (T);
   --  @param T any type
   --  @return the representative of the base type of T, or the result of
   --    Base_Retysp on this representative if it is a subtype.

   --  The following functions provide wrappers for the query functions in
   --  Einfo, that apply the query on the "Representative Type in SPARK" of
   --  its argument, hence skipping all layers of private types. To avoid
   --  confusion, the wrapper for function Einfo.Is_Such_And_Such_Type is
   --  called Has_Such_And_Such_Type.

   function Has_Array_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Array_Kind);

   function Has_Boolean_Type (T : Entity_Id) return Boolean is
     (Root_Type (Retysp (T)) = Standard_Boolean);

   function Has_Class_Wide_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Class_Wide_Kind);

   function Has_Composite_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Composite_Kind);

   function Has_Discrete_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Discrete_Kind);

   function Has_Enumeration_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Enumeration_Kind);

   function Has_Modular_Integer_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Modular_Integer_Kind);

   function Has_Record_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Record_Kind);

   function Has_Private_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Private_Kind);

   function Has_Scalar_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Scalar_Kind);

   function Has_Signed_Integer_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Signed_Integer_Kind);

   function Has_Fixed_Point_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Fixed_Point_Kind);

   function Has_Floating_Point_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Float_Kind);

   function Has_Single_Precision_Floating_Point_Type (T : Entity_Id)
                                                      return Boolean is
     (Is_Single_Precision_Floating_Point_Type (Retysp (T)));

   function Has_Double_Precision_Floating_Point_Type (T : Entity_Id)
                                                      return Boolean is
     (Is_Double_Precision_Floating_Point_Type (Retysp (T)));

   function Has_Static_Scalar_Subtype (T : Entity_Id) return Boolean;
   --  Returns whether type T has a scalar subtype with statically known
   --  bounds. This includes looking past private types.

   -------------------------------
   -- General Queries For Types --
   -------------------------------

   function Can_Be_Default_Initialized (Typ : Entity_Id) return Boolean is
     ((not Has_Array_Type (Typ) or else Is_Constrained (Typ))
      and then (not (Retysp_Kind (Typ) in
                         Record_Kind | Private_Kind | Concurrent_Kind)
                or else not Has_Discriminants (Typ)
                or else Is_Constrained (Typ)
                or else Has_Defaulted_Discriminants (Typ))
      and then not Is_Class_Wide_Type (Typ));
   --  Determine whether there can be default initialized variables of a type.
   --  @param Typ any type
   --  @return False if Typ is unconstrained.

   function Check_Needed_On_Conversion (From, To : Entity_Id) return Boolean;
   --  @param From type of expression to be converted, which should be a Retysp
   --  @param To target type of the conversion, which should be a Retysp
   --  @return whether a check may be needed when converting an expression
   --     of type From to type To. Currently a very coarse approximation
   --     to rule out obvious cases.

   function Default_Initialization
     (Typ           : Entity_Id;
      Explicit_Only : Boolean := False) return Default_Initialization_Kind;
   --  Determine default initialization kind that applies to a particular type.
   --  Types defined in units with external axiomatization (such as formal
   --  containers) and private types are treated specially, so that they are
   --  either considered as having full default initialization, or no default
   --  initialization.
   --  @param Typ any type
   --  @param Explicit_Only If True then do not consider attributes
   --    Has_DIC and Has_Inherited_DIC for this
   --    type.
   --  @return the Default_Initialization_Kind of Typ

   function Find_Predicate_Aspect (Typ : Entity_Id) return Node_Id;
   --  Find the aspect specification Predicate or Dynamic_Predicate or
   --  Static_Predicate associated with entity Typ. Return Empty if Typ does
   --  not have any of these aspects. Typ might still inherit the aspect in
   --  such cases.
   --  This is only used to give better locations for error messages. To get
   --  the predicate expression, use the procedure generated to check the
   --  predicate.

   function Get_Initial_DIC_Procedure (E : Entity_Id) return Entity_Id with
     Pre => Is_Type (E) and then Has_DIC (E);
   --  @param E a type with a DIC
   --  @return the DIC procedure defined on the ancestor of E which has a body
   --     if any. This is necessary as inherited DIC procedures don't have a
   --     body.

   function Get_Full_Type_Without_Checking (N : Node_Id) return Entity_Id
   with Pre => Present (N);
   --  Get the type of the given entity. This function looks through
   --  private types and should be used with extreme care.
   --  ??? This function should probably be removed. Its comment says it
   --  applies to entities, while it may be called from flow on entities or
   --  nodes of record type.

   function Get_Iterable_Type_Primitive
     (Typ : Entity_Id;
      Nam : Name_Id) return Entity_Id;
   --  Retrieve one of the primitives First, Next, Has_Element, Element from
   --  the value of the Iterable aspect of a formal type.
   --  Return the ultimate alias.

   function Has_Invariants_In_SPARK (E : Entity_Id) return Boolean;
   --  @params E any type
   --  @returns True if E has a type invariant and the invariant is in SPARK.

   function Has_Static_Discrete_Predicate (E : Entity_Id) return Boolean;
   --  @param E any type
   --  @return True iff E is a discrete type with a static predicate

   function Has_Visible_Type_Invariants (Ty : Entity_Id) return Boolean;
   --  @param Ty type entity
   --  @return True if Ty has a top level invariant which needs to be checked
   --          in the current compilation unit and False if it can be assumed
   --          to hold.
   --  Since invariants can only be declared directly in compilation units, it
   --  is enough to check if the type is declared in the main compilation unit
   --  to decide whether or not it should be checked in this unit.

   function Invariant_Check_Needed (Ty : Entity_Id) return Boolean;
   --  @param Ty type entity
   --  @return True if there is an invariant that needs to be checked for type
   --          Ty. It can come from Ty itself, from one of its ancestors, or
   --          from one of its components.

   function Is_Nouveau_Type (T : Entity_Id) return Boolean is
     (Etype (T) = T);
   --  @param T any type
   --  @return True iff T is neither a derived type, nor a subtype, nor
   --     a classwide type (see description of Etype field in einfo.ads),
   --     something generally useful to know in gnat2why, that we call being
   --     a "nouveau" type. [Calling it a "new" type would be confusing with
   --     derived types.]

   function Is_Null_Range (T : Entity_Id) return Boolean;
   --  @param T any type
   --  @returns True iff T is a scalar type whose range is statically known to
   --     be empty

   function Is_Standard_Boolean_Type (E : Entity_Id) return Boolean;
   --  @param E type
   --  @return True if we can determine that E is Standard_Boolean or a subtype
   --    of Standard_Boolean which also ranges over False .. True

   function Needs_Default_Checks_At_Decl (E : Entity_Id) return Boolean with
     Pre => Is_Type (E);
   --  @param E type
   --  @return True if E needs a specific module to check its default
   --     expression at declaration.

   --------------------------------
   -- Queries related to records --
   --------------------------------

   function Count_Non_Inherited_Discriminants
     (Assocs : List_Id) return Natural;
   --  @param Assocs list of component associations
   --  @return the number of discriminants used as choices in Assocs, ignoring
   --     those that are inherited from a parent type

   --  ??? Add a precondition to Count_Why_Regular_Fields and
   --  Count_Why_Top_Level_Fields that Retysp (E) = E ?

   function Get_Specific_Type_From_Classwide (E : Entity_Id) return Entity_Id
   with Pre => Is_Class_Wide_Type (E);
   --  Returns the specific type associated with a class wide type.
   --  If E's Etype is a fullview, returns its partial view instead.
   --  For classwide subtypes, return their Etype's specific type.
   --  ??? This should make the mechanism with the extra table
   --  Specific_Tagged_Types redundant, except the detection that a type is
   --  a full view is currently not available soon enough.

   function Get_Stored_Constraint_For_Discr
     (Ty    : Entity_Id;
      Discr : Entity_Id)
      return Node_Id
   with Pre => Has_Discriminants (Ty) and then Is_Constrained (Ty);
   --  @param Ty a constrained type with discriminants
   --  @param Discr a discriminant of Ty
   --  @return the constraint stored for Discr in Ty

   function Has_Private_Ancestor_Or_Root (E : Entity_Id) return Boolean;
   --  @param E any type
   --  @return True iff E is a tagged type whose translation into Why3 requires
   --     the use of an ancestor field, to denote invisible fields from an
   --     ancestor at the Why3 level (due either to a private ancestor or
   --     a root type whose full view not in SPARK).

   function Has_Private_Fields (E : Entity_Id) return Boolean with
     Pre => Has_Private_Type (E) or else Has_Record_Type (E);
   --  @param E a private or record type
   --  @return True iff E's translation into Why3 requires the use of a main
   --     field to represent invisible fields that are not derived from an
   --     ancestor.

   function Root_Record_Type (E : Entity_Id) return Entity_Id;
   --  Given a record type (or private type whose implementation is a record
   --  type, etc.), return the root type, including traversing private types.
   --  ??? Need to update comment to reflect dependence on Retysp of root by
   --  calling Full_View_Not_In_SPARK.

   function Is_Ancestor (Anc : Entity_Id; E : Entity_Id) return Boolean is
     (if not Is_Class_Wide_Type (Anc) then Sem_Type.Is_Ancestor (Anc, E)
      else Sem_Type.Is_Ancestor (Get_Specific_Type_From_Classwide (Anc), E));
   --  @param Anc A tagged type (which may or not be class-wide).
   --  @param E A tagged type (which may or not be class-wide).
   --  @return True if Anc is one of the ancestors of type E.

   --------------------------------
   -- Queries related to arrays --
   --------------------------------

   function Is_Static_Array_Type (E : Entity_Id) return Boolean;
   --  @param E any type
   --  @return True iff E is a constrained array type with statically known
   --     bounds

   function Has_Static_Array_Type (T : Entity_Id) return Boolean is
     (Is_Static_Array_Type (Retysp (T)));

   function Nth_Index_Type (E : Entity_Id; Dim : Positive) return Node_Id
   with Pre => Is_Array_Type (E);
   --  @param E array type
   --  @param Dim dimension
   --  @return the argument E in the special case where E is a string literal
   --    subtype; otherwise the index type entity which corresponds to the
   --    selected dimension

   function Static_Array_Length (E : Entity_Id; Dim : Positive) return Uint
   with Pre => Is_Static_Array_Type (E);
   --  @param E constrained array type with statically known bounds
   --  @param Dim dimension
   --  @return the static length of dimension Dim of E

   -----------------------------------
   -- Queries related to task types --
   -----------------------------------

   function Private_Declarations_Of_Task_Type (E : Entity_Id) return List_Id
   with Pre => Ekind (E) = E_Task_Type;
   --  @param E a task type entity
   --  @return the list of visible declarations of the task type, or the empty
   --    list of not available

   function Task_Body (E : Entity_Id) return Node_Id
   with Pre  => Ekind (E) = E_Task_Type,
        Post => (if Present (Task_Body'Result)
                 then Nkind (Task_Body'Result) = N_Task_Body);
   --  @param E task type
   --  @return the task body for the given type, similar to what
   --    Subprogram_Body might produce.

   function Task_Body_Entity (E : Entity_Id) return Entity_Id
   with Pre  => Ekind (E) = E_Task_Type,
        Post => (if Present (Task_Body_Entity'Result)
                 then Ekind (Task_Body_Entity'Result) = E_Task_Body);
   --  @param E task type
   --  @return the entity of the task body for the given type, similar
   --    to what Subprogram_Body_Entity might produce.

   function Task_Type_Definition (E : Entity_Id) return Node_Id
   is (Task_Definition (Parent (E)))
   with Pre  => Ekind (E) = E_Task_Type,
        Post => (if Present (Task_Type_Definition'Result) then
                 Nkind (Task_Type_Definition'Result) = N_Task_Definition);
   --  @param E a task type entity
   --  @return the definition of the task type

   function Visible_Declarations_Of_Task_Type (E : Entity_Id) return List_Id
   with Pre => Ekind (E) = E_Task_Type;
   --  @param E a task type entity
   --  @return the list of visible declarations of the task type, or the empty
   --    list if not available

   ----------------------------------------
   -- Queries related to protected types --
   ----------------------------------------

   function Private_Declarations_Of_Prot_Type (E : Entity_Id) return List_Id
   with Pre => Is_Protected_Type (E);
   --  @param E a protected type entity
   --  @return the list of visible declarations of the protected type

   function Protected_Body (E : Entity_Id) return Node_Id
   with Pre  => Ekind (E) = E_Protected_Type,
        Post => (if Present (Protected_Body'Result)
                 then Nkind (Protected_Body'Result) = N_Protected_Body);
   --  @param E protected type
   --  @return the protected body for the given type, similar to what
   --    subprogram_body might produce.

   function Protected_Type_Definition (E : Entity_Id) return Node_Id
   with Pre  => Ekind (E) = E_Protected_Type,
        Post => (if Present (Protected_Type_Definition'Result)
                 then Nkind (Protected_Type_Definition'Result) =
                        N_Protected_Definition);
   --  @param E protected type
   --  @return the protected definition for the given type

   function Requires_Interrupt_Priority (E : Entity_Id) return Boolean
   with Pre => Ekind (E) = E_Protected_Type;
   --  @param E the entity of a protected type
   --  @return True if E contains a protected procedure with Attach_Handler
   --  specified. Note that Interrupt_Handler cannot be True with the Ravenscar
   --  profile.

   function Visible_Declarations_Of_Prot_Type (E : Entity_Id) return List_Id
   with Pre => Is_Protected_Type (E);
   --  @param E a protected type entity
   --  @return the list of visible declarations of the protected type

end SPARK_Util.Types;
