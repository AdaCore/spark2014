------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      S P A R K _ U T I L - T Y P E S                     --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2016-2022, AdaCore                     --
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

package SPARK_Util.Types is

   ---------------------------------------------
   -- Queries related to representative types --
   ---------------------------------------------

   --  A type may be in SPARK even if its most underlying type (the one
   --  obtained by following the chain of Underlying_Type) is not in SPARK.
   --  In the simplest case, a private type may have its partial view in SPARK
   --  and its full view not in SPARK. In other cases, such a private type will
   --  be found on the chain of type derivation and subtyping from the most
   --  underlying type to the current type.

   --  The "Representative Type in SPARK" (Retysp for short) of a type T is
   --  the type that represents T in the translation into Why3. It is the most
   --  underlying type of T when it is in SPARK, or the first private type on
   --  the chain of Underlying_Type links at the boundary between SPARK and
   --  non-SPARK. For non-private types, Retysp is the identity.s

   function Retysp (T : Type_Kind_Id) return Type_Kind_Id;
   --  @param T any type
   --  @return the "Representative Type in SPARK" of type T
   --  It should only be called on marked type entities (except for Itypes).

   function Retysp_Kind (T : Type_Kind_Id) return Type_Kind;
   --  @param T any type
   --  @return the entity kind of the "Representative Type in SPARK" of type T.

   function Base_Retysp (T : Type_Kind_Id) return Type_Kind_Id;
   --  @param T any type
   --  @return the representative of the base type of T, or the result of
   --    Base_Retysp on this representative if it is a subtype.

   --  The following functions provide wrappers for the query functions in
   --  Einfo, that apply the query on the "Representative Type in SPARK" of
   --  its argument, hence skipping all layers of private types. To avoid
   --  confusion, the wrapper for function Einfo.Is_Such_And_Such_Type is
   --  called Has_Such_And_Such_Type.

   function Has_Access_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Access_Kind);

   function Has_Array_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Array_Kind);

   function Has_Boolean_Type (T : Type_Kind_Id) return Boolean is
     (Root_Type (Retysp (T)) = Standard_Boolean);

   function Has_Discrete_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Discrete_Kind);

   function Has_Integer_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Integer_Kind);

   function Has_Modular_Integer_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Modular_Integer_Kind);

   function Has_Record_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Record_Kind);

   function Has_Incomplete_Or_Private_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Incomplete_Or_Private_Kind);

   function Has_Scalar_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Scalar_Kind);

   function Has_Signed_Integer_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Signed_Integer_Kind);

   function Has_Fixed_Point_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Fixed_Point_Kind);

   function Has_Floating_Point_Type (T : Type_Kind_Id) return Boolean is
     (Retysp_Kind (T) in Float_Kind);

   function Has_Single_Precision_Floating_Point_Type
     (T : Type_Kind_Id)
      return Boolean
   is (Is_Single_Precision_Floating_Point_Type (Retysp (T)));

   function Has_Double_Precision_Floating_Point_Type
     (T : Type_Kind_Id)
      return Boolean
   is (Is_Double_Precision_Floating_Point_Type (Retysp (T)));

   function Has_Extended_Precision_Floating_Point_Type
     (T : Type_Kind_Id)
      return Boolean
   is (Is_Extended_Precision_Floating_Point_Type (Retysp (T)));

   function Has_Static_Predicate (T : Type_Kind_Id) return Boolean is
     (Einfo.Entities.Has_Static_Predicate (Retysp (T)));

   function Static_Discrete_Predicate (T : Type_Kind_Id) return List_Id is
     (Einfo.Entities.Static_Discrete_Predicate (Retysp (T)));

   function Has_Static_Scalar_Subtype (T : Type_Kind_Id) return Boolean with
     Pre => Has_Scalar_Type (T);
   --  Returns whether type T has a scalar subtype with statically known
   --  bounds. This includes looking past private types.

   -------------------------------
   -- General Queries For Types --
   -------------------------------

   function Can_Be_Default_Initialized (Typ : Type_Kind_Id) return Boolean is
     ((not Has_Array_Type (Typ) or else Is_Constrained (Typ))
      and then (Retysp_Kind (Typ) not in
                   Record_Kind | Incomplete_Or_Private_Kind | Concurrent_Kind
                or else not Has_Discriminants (Typ)
                or else Is_Constrained (Typ)
                or else Has_Defaulted_Discriminants (Typ))
      and then not Is_Class_Wide_Type (Typ));
   --  Determine whether there can be default initialized variables of a type.
   --  @param Typ any type
   --  @return False if Typ is unconstrained.

   function Check_Needed_On_Conversion
     (From, To : Type_Kind_Id)
      return Boolean;
   --  @param From type of expression to be converted
   --  @param To target type of the conversion
   --  @return whether a check may be needed when converting an expression
   --     of type From to type To. Currently a very coarse approximation
   --     to rule out obvious cases.

   function Unchecked_Full_Type (E : Type_Kind_Id) return Type_Kind_Id
   with Post => not Is_Private_Type (Unchecked_Full_Type'Result);
   --  Get the type of the given entity. This function looks through private
   --  types and should be used with extreme care.

   function Use_Predefined_Equality_For_Type
     (Typ : Type_Kind_Id)
      return Boolean;
   --  Return True if membership tests and equality of components of
   --  composite types of type Typ use the predefined equality and not the
   --  primitive one (ie. Type is not an unlimited record type or it does
   --  not have a redefined equality).

   function Use_Real_Eq_For_Private_Type (E : Type_Kind_Id) return Boolean
   with Pre => Is_Incomplete_Or_Private_Type (E)
     or else Is_Concurrent_Type (E);
   --  Return True if the predefined equality on a private type opaque for
   --  SPARK can be represented using Why3 equality.

   function Get_Parent_Type_If_Check_Needed
     (N : N_Declaration_Id)
      return Opt_Type_Kind_Id
   with Pre => Nkind (N) in N_Full_Type_Declaration | N_Subtype_Declaration;
   --  @param N a (sub)type declaration
   --  @return If the type declaration requires a check, return the "parent"
   --    type mentionend in the type declaration. Return empty otherwise.

   function Has_Invariants_In_SPARK (E : Type_Kind_Id) return Boolean;
   --  @params E any type
   --  @returns True if E has a type invariant and the invariant is in SPARK.

   function Has_Unconstrained_UU_Component (Typ : Type_Kind_Id) return Boolean;
   --  Returns True iff Typ has a component visible in SPARK whose type is an
   --  unchecked union type which is unconstrained. Predefined equality on
   --  these types is defined to raise Program_Error in Ada for now, even if
   --  the primitive equality of the components is redefined. To be changed
   --  when the wording and the compiler are fixed (code might be shared with
   --  Predefined_Eq_Uses_Pointer_Eq).
   --  Should be called on marked types.

   function Has_Visible_Type_Invariants (Ty : Type_Kind_Id) return Boolean;
   --  @param Ty type entity
   --  @return True if Ty has a top level invariant which needs to be checked
   --          in the current compilation unit and False if it can be assumed
   --          to hold.
   --  Since invariants can only be declared directly in compilation units, it
   --  is enough to check if the type is declared in the main compilation unit
   --  to decide whether or not it should be checked in this unit.

   function Invariant_Check_Needed (Ty : Type_Kind_Id) return Boolean;
   --  @param Ty type entity
   --  @return True if there is an invariant that needs to be checked for type
   --          Ty. It can come from Ty itself, from one of its ancestors, or
   --          from one of its components.

   function May_Need_DIC_Checking (E : Type_Kind_Id) return Boolean;
   --  @param E type entity
   --  @return True iff E is the entity for a declaration that may require
   --     checking the DIC. This only occurs if E has its own DIC, as
   --     primitive subprograms of tagged types cannot be called in their DIC
   --     so it is not necessary to recheck them on tagged derivations.

   function Check_DIC_At_Declaration (E : Type_Kind_Id) return Boolean
     with Pre => Present (Partial_DIC_Procedure (E));
   --  @param E type entity with a DIC (inherited or not)
   --  @return True if the DIC expression depends on the current type instance.
   --        If it depends on the type instance, it is considered as a
   --        postcondtion of the default initialization of the private type
   --        and is checked at declaration. Otherwise, it is considered as a
   --        precondition of the default initialization, and is checked at use.

   function Is_Anonymous_Access_Object_Type (T : Type_Kind_Id) return Boolean
   is (Ekind (T) = E_Anonymous_Access_Type);

   function Is_General_Access_Type (T : Type_Kind_Id) return Boolean;
   --  @param T any type
   --  @returns True iff T is (a subtype of) a general access-to-variable type

   function Is_Nouveau_Type (T : Type_Kind_Id) return Boolean is
     (Etype (T) = T);
   --  @param T any type
   --  @return True iff T is neither a derived type, nor a subtype, nor
   --     a classwide type (see description of Etype field in einfo.ads),
   --     something generally useful to know in gnat2why, that we call being
   --     a "nouveau" type. [Calling it a "new" type would be confusing with
   --     derived types.]

   function Is_Null_Range (T : Type_Kind_Id) return Boolean;
   --  @param T any type
   --  @returns True iff T is a scalar type whose range is statically known to
   --     be empty

   function Is_Standard_Boolean_Type (E : Type_Kind_Id) return Boolean;
   --  @param E type
   --  @return True if we can determine that E is Standard_Boolean or a subtype
   --    of Standard_Boolean which also ranges over False .. True.
   --    Always return False if the type might be contained in a type with
   --    relaxed initialization.

   function Is_Standard_Type (E : Type_Kind_Id) return Boolean;
   --  Returns True iff type E is declared in Standard

   function Is_System_Address_Type (E : Type_Kind_Id) return Boolean;
   --  Returns True iff type E is System.Address

   function Needs_Default_Checks_At_Decl (E : Type_Kind_Id) return Boolean;
   --  @param E type
   --  @return True if E needs a specific module to check its default
   --     expression at declaration.

   function Is_Deep (Typ : Type_Kind_Id) return Boolean;
   --  Returns True if the type passed as argument is deep (ie. it has
   --  subcomponents of an access-to-variable type or a private type annotated
   --  with ownership).

   procedure Find_Predicate_Item
     (Ty       :        Type_Kind_Id;
      Rep_Item : in out Node_Id);
   --  Go over the items linked from Rep_Item to search for a predicate
   --  pragma or aspect applying to Ty.

   procedure Suitable_For_UC
     (Typ         :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  This procedure implements the notion of "suitable for unchecked
   --  conversion" of SPARK RM 13.9.

   procedure Suitable_For_UC_Target
     (Typ         :     Type_Kind_Id;
      Use_Esize   :     Boolean;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  This procedure implements the notion of "suitable as a target of an
   --  unchecked conversion" of SPARK RM 13.9.

   procedure Have_Same_Known_Esize
     (A, B        :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  If types A and B have the same Esize, then set Result to True; otherwise
   --  set Result to False and Explanation to a possible fix.

   procedure Have_Same_Known_RM_Size
     (A, B        :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  Same as Have_Same_Known_Esize, but checks the RM_Size.

   function Contains_Access_Subcomponents (Typ : Type_Kind_Id) return Boolean;
   --  Returns True if Typ has access subcomponents

   function Contains_Allocated_Parts (Typ : Type_Kind_Id) return Boolean
     with Post => (if Contains_Allocated_Parts'Result then Is_Deep (Typ));
   --  Returns True if Typ has subcomponents whose type is a pool specific
   --  access type or a private type annotated with ownership which needs
   --  reclamation (and these subcomponents are not in a constant part of Typ).

   function Contains_Relaxed_Init_Parts
     (Typ        : Type_Kind_Id;
      Ignore_Top : Boolean := False)
      return Boolean
   with
     Post => (if Contains_Relaxed_Init_Parts'Result
              then Might_Contain_Relaxed_Init (Typ));
   --  Returns True if Typ has subcomponents whose type is annotated with
   --  relaxed initialization.
   --  If Ignore_Top is True, ignore a potential Relaxed_Initialization
   --  aspect on the type itself.

   function Contains_Only_Relaxed_Init (Typ : Type_Kind_Id) return Boolean
   with
     Post => (if Contains_Only_Relaxed_Init'Result
              then Contains_Relaxed_Init_Parts (Typ));
   --  Returns True if Typ has at least a subcomponent whose type is annotated
   --  with relaxed initialization, all its scalar subcomponents have this
   --  annotation and it contains no predicates.
   --  These types are considered to have relaxed initialization even if they
   --  don't have the aspect.

   function Might_Contain_Relaxed_Init (Typ : Type_Kind_Id) return Boolean;
   --  Returns True if Typ has subcomponents whose type may be used for
   --  expressions with relaxed initialization.

   function Num_Literals (Ty : Enumeration_Kind_Id) return Positive;
   --  Returns the number of literals for an enumeration type

   function Parent_Type (Ty : Type_Kind_Id) return Opt_Type_Kind_Id;
   --  Compute the first parent in the derivation tree of Ty if any. Otherwise
   --  return Etype (Ty). This also takes into account subtypes.

   function Parent_Retysp (Ty : Type_Kind_Id) return Opt_Type_Kind_Id;
   --  Compute the first parent in the derivation tree of Ty if any. Otherwise
   --  return Empty. This also takes into account subtypes, and only considers
   --  derivations visible from SPARK code (using Retysp).

   generic
      with procedure Process_DIC_Expression
        (Type_Instance  : Formal_Kind_Id;
         DIC_Expression : Node_Id);
   procedure Iterate_Applicable_DIC (Ty : Type_Kind_Id);
   --  Traverse all default initial conditions associated to the type Ty

   generic
      with procedure Process_Pred_Expression
        (Type_Instance   : Formal_Kind_Id;
         Pred_Expression : Node_Id);
   procedure Iterate_Applicable_Predicates (Ty : Type_Kind_Id);
   --  Traverse all predicates associated to the type Ty

   function Predefined_Eq_Uses_Pointer_Eq (Ty : Type_Kind_Id) return Boolean
     with Pre => not Is_Concurrent_Type (Retysp (Ty));
   --  Return True if the predefined equality of Ty uses the predefined
   --  equality on access types.

   function Acts_As_Incomplete_Type (Ty : Type_Kind_Id) return Boolean;
   --  Return True if Ty is is handled as an incomplete type to decide whether
   --  the type designated by an access type should be deferred.

   function Is_Derived_Type_With_Null_Ext (Ty : Type_Kind_Id) return Boolean
   with Ghost;
   --  Return True if Ty is declared as a derived type with a null record
   --  extension. It is only used in assertions currently.

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

   function Get_Specific_Type_From_Classwide
     (E : Class_Wide_Kind_Id)
      return Type_Kind_Id;
   --  Returns the specific type associated with a class wide type.
   --  If E's Etype is a fullview, returns its partial view instead.
   --  For classwide subtypes, return their Etype's specific type.
   --  ??? This should make the mechanism with the extra table
   --  Specific_Tagged_Types redundant, except the detection that a type is
   --  a full view is currently not available soon enough.

   function Get_Constraint_For_Discr
     (Ty    : Type_Kind_Id;
      Discr : E_Discriminant_Id)
      return N_Subexpr_Id
   with Pre => Has_Discriminants (Ty)
               and then Is_Constrained (Ty);
   --  @param Ty a constrained type with discriminants
   --  @param Discr a discriminant of Ty
   --  @return the constraint for Discr in Ty

   function Get_User_Defined_Eq (Typ : Type_Kind_Id) return Opt_E_Function_Id;
   --  Same as Sem_Util.Get_User_Defined_Eq except that it goes through
   --  renamings and ignores predefined equality of tagged types.

   function Has_Private_Fields (E : Type_Kind_Id) return Boolean
     with Pre => Has_Incomplete_Or_Private_Type (E)
        or else Has_Record_Type (E);
   --  @param E a private or record type
   --  @return True iff E's translation into Why3 requires the use of a main
   --     field to represent invisible fields that are not derived from an
   --     ancestor.

   function Root_Retysp (E : Type_Kind_Id) return Type_Kind_Id;
   --  Given a type, return the root type, including traversing private types.
   --  ??? Need to update comment to reflect dependence on Retysp of root by
   --  calling Full_View_Not_In_SPARK.

   function Is_Ancestor (Anc, E : Type_Kind_Id) return Boolean is
     (if not Is_Class_Wide_Type (Anc) then Sem_Type.Is_Ancestor (Anc, E)
      else Sem_Type.Is_Ancestor (Get_Specific_Type_From_Classwide (Anc), E));
   --  @param Anc A tagged type (which may or not be class-wide).
   --  @param E A tagged type (which may or not be class-wide).
   --  @return True if Anc is one of the ancestors of type E.

   --------------------------------
   -- Queries related to arrays --
   --------------------------------

   function Is_Static_Array_Type (E : Type_Kind_Id) return Boolean;
   --  @param E any type
   --  @return True iff E is a constrained array type with statically known
   --     bounds

   function Has_Static_Array_Type (T : Type_Kind_Id) return Boolean is
     (Is_Static_Array_Type (Retysp (T)));

   function Nth_Index_Type
     (E   : Array_Kind_Id;
      Dim : Positive)
      return Type_Kind_Id;
   --  @param E array type
   --  @param Dim dimension
   --  @return the argument E in the special case where E is a string literal
   --    subtype; otherwise the index type entity which corresponds to the
   --    selected dimension

   function Static_Array_Length (E : Array_Kind_Id; Dim : Positive) return Uint
     with Pre => Is_Static_Array_Type (E);
   --  @param E constrained array type with statically known bounds
   --  @param Dim dimension
   --  @return the static length of dimension Dim of E

   -----------------------------------
   -- Queries related to task types --
   -----------------------------------

   function Private_Declarations_Of_Task_Type
     (E : E_Task_Type_Id)
      return List_Id;
   --  @param E a task type entity
   --  @return the list of visible declarations of the task type, or the empty
   --    list of not available

   function Task_Body (E : E_Task_Type_Id) return Opt_N_Task_Body_Id;
   --  @param E task type
   --  @return the task body for the given type, similar to what
   --    Subprogram_Body might produce.

   function Task_Body_Entity (E : E_Task_Type_Id) return Opt_E_Task_Body_Id;
   --  @param E task type
   --  @return the entity of the task body for the given type, similar
   --    to what Subprogram_Body_Entity might produce.

   function Task_Type_Definition
     (E : E_Task_Type_Id)
      return Opt_N_Task_Definition_Id
   is (Task_Definition (Parent (E)));
   --  @param E a task type entity
   --  @return the definition of the task type

   function Visible_Declarations_Of_Task_Type
     (E : E_Task_Type_Id)
      return List_Id;
   --  @param E a task type entity
   --  @return the list of visible declarations of the task type, or the empty
   --    list if not available

   ----------------------------------------
   -- Queries related to protected types --
   ----------------------------------------

   function Private_Declarations_Of_Prot_Type
     (E : Protected_Kind_Id)
      return List_Id;
   --  @param E a protected type entity
   --  @return the list of visible declarations of the protected type

   function Protected_Body
     (E : Protected_Kind_Id)
      return Opt_N_Protected_Body_Id;
   --  @param E protected type
   --  @return the protected body for the given type, similar to what
   --    subprogram_body might produce.

   function Protected_Type_Definition
     (E : Protected_Kind_Id)
      return Opt_N_Protected_Definition_Id;
   --  @param E protected type
   --  @return the protected definition for the given type

   function Requires_Interrupt_Priority
     (E : Protected_Kind_Id)
      return Boolean;
   --  @param E the entity of a protected type
   --  @return True if E contains a protected procedure with Attach_Handler
   --  specified. Note that Interrupt_Handler cannot be True with the Ravenscar
   --  profile.

   function Visible_Declarations_Of_Prot_Type
     (E : Protected_Kind_Id)
      return List_Id;
   --  @param E a protected type entity
   --  @return the list of visible declarations of the protected type

end SPARK_Util.Types;
