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

with AA_Util;           use AA_Util;
with Atree;             use Atree;
with Common_Containers; use Common_Containers;
with Einfo;             use Einfo;
with Impunit;           use Impunit;
with Lib;               use Lib;
with Namet;             use Namet;
with Sem_Type;
with Sem_Util;          use Sem_Util;
with Sinfo;             use Sinfo;
with Sinput;            use Sinput;
with Snames;            use Snames;
with Stand;             use Stand;
with Types;             use Types;
with Uintp;             use Uintp;
with Why.Atree.Tables;  use Why.Atree.Tables;

package SPARK_Util is

   ---------------------------------------------------
   --  Utility types related to entities and nodes  --
   ---------------------------------------------------

   --  The following type lists all possible kinds of default initialization
   --  that may apply to a type.

   type Default_Initialization_Kind is
     (No_Possible_Initialization,
      --  A type cannot possibly be initialized because it has no content, for
      --  example - a null record.

      Full_Default_Initialization,
      --  A type that combines the following types and content:
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
      --  A type where some of its internals are fully default initialized and
      --  some are not.

      No_Default_Initialization
      --  A type where none of its content is fully default initialized
     );

   type Execution_Kind_T is
     (Normal_Execution,      --  regular subprogram
      Barrier,               --  conditional execution
      Abnormal_Termination,  --  No_Return, no output
      Infinite_Loop);        --  No_Return, some output
   --  Expected kind of execution for a called procedure. This does not apply
   --  to main procedures, which should not be called.
   --
   --  Please be *exceptionally* alert when adding elements to this type,
   --  as many checks simply check for one of the options (and do not
   --  explicitly make sure all cases are considered).

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

   ------------------------------
   -- Extra tables on entities --
   ------------------------------

   --  The information provided by the frontend is not always sufficient. For
   --  GNATprove, we need in particular:

   --  - the link from the full view to the partial view for private types and
   --    deferred constants (the GNAT tree only contains the opposite link in
   --    Full_View)
   --  - the link from a classwide type to the corresponding specific tagged
   --    type

   --  We store this additional information in extra tables during the SPARK
   --  checking phase, so that it's available during flow analysis and proof.

   procedure Set_Partial_View (E, V : Entity_Id);
   --  Create a link from the full view to the partial view of an entity.
   --  @param E full view of private type or deferred constant
   --  @param V partial view of the same private type or deferred constant

   function Partial_View (E : Entity_Id) return Entity_Id;
   --  @param E type or constant
   --  @return if E is the full view of a private type or deferred constant,
   --    return the partial view for entity E, otherwise Empty

   function Is_Full_View (E : Entity_Id) return Boolean;
   --  @param E type or constant
   --  @return True iff E is the full view of a private type or deferred
   --     constant

   function Is_Partial_View (E : Entity_Id) return Boolean;
   --  @param E type or constant
   --  @return True iff E is the partial view of a private type or deferred
   --     constant

   procedure Set_Specific_Tagged (E, V : Entity_Id);
   --  Create a link from the classwide type to its specific tagged type
   --  in SPARK, which can be either V or its partial view if the full view of
   --  V is not in SPARK.
   --  @param E classwide type
   --  @param V specific tagged type corresponding to the classwide type E

   function Specific_Tagged (E : Entity_Id) return Entity_Id;
   --  @param E classwide type
   --  @return the specific tagged type corresponding to classwide type E

   ------------------------------------------------
   -- Queries related to external axiomatization --
   ------------------------------------------------

   --  Units for which External_Axiomatization is specified have their
   --  translation into Why3 defined manually, so much of the treatments in
   --  gnat2why have to be adopted for the entities defined in such units.
   --  Currently, only the (generic) formal containers in the standard library
   --  are using this mechanism.

   function Entity_In_Ext_Axioms (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E is declared in a package with external axiomatization

   function Is_Access_To_Ext_Axioms_Discriminant
     (N : Node_Id) return Boolean
     with Pre => Nkind (N) = N_Selected_Component;
   --  @param N selected component node
   --  @return True iff the selector is a discriminant of a type defined in
   --     a package with external axiomatization.

   function Is_Ext_Axioms_Discriminant (E : Entity_Id) return Boolean
     with Pre => Ekind (E) = E_Discriminant;
   --  @param E discriminant
   --  @return True iff E is the discriminant of a type defined in a package
   --     with external axiomatization.

   function Package_Has_Ext_Axioms (E : Entity_Id) return Boolean
     with Pre => Is_Package_Or_Generic_Package (E);
   --  @param E (possibly generic) package
   --  @return True iff E is a package with external axiomatization

   function Type_Based_On_Ext_Axioms (E : Entity_Id) return Boolean;
   --  @param E type
   --  @return True iff E is a private type defined in a package with external
   --     axiomatization, or a subtype/derived type from such a type.

   function Underlying_Ext_Axioms_Type (E : Entity_Id) return Entity_Id;
   --  @param E type
   --  @return if E is a private type defined in a package with external
   --     axiomatization, or a subtype/derived type from such a type, return
   --     that type, otherwise Empty.

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

   function Retysp_Kind (T : Entity_Id) return Entity_Kind
   with Pre => Is_Type (T);
   --  @param T any type
   --  @return the entity kind of the "Representative Type in SPARK" of type T.
   --     This is not the same as Ekind (Retysp (T)), because Retysp (T) may
   --     be a private type, and we're interested here in the underlying kind
   --     of type.

   --  The following functions provide wrappers for the query functions in
   --  Einfo, that apply the query on the "Representative Type in SPARK" of its
   --  argument, hence skipping all layers of pivate types. To avoid confusion,
   --  the wrapper for function Einfo.Is_Such_And_Such_Type is called
   --  Has_Such_And_Such_Type.

   function Has_Access_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Access_Kind);

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

   function Has_Scalar_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Scalar_Kind);

   function Has_Signed_Integer_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Signed_Integer_Kind);

   function Has_Fixed_Point_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Fixed_Point_Kind);

   function Has_Floating_Point_Type (T : Entity_Id) return Boolean is
     (Retysp_Kind (T) in Float_Kind);

   function Has_Static_Scalar_Subtype (T : Entity_Id) return Boolean;
   --  Returns whether type T has a scalar subtype with statically known
   --  bounds. This included looking past private types.

   ---------------------------------
   -- Queries related to entities --
   ---------------------------------

   function Analysis_Requested
     (E            : Entity_Id;
      With_Inlined : Boolean) return Boolean;
   --  @param E subprogram, task or package
   --  @param With_Inlined True if inlined subprograms should be analyzed
   --  @return True iff subprogram, task or package E must be analyzed,
   --     because it belongs to one of the analyzed units, and either the
   --     complete unit is analyzed, or E is the specific entity whose analysis
   --     was requested.
   --
   --  With_Inlined is set to False in proof to avoid analyzing when possible
   --  subprograms that are inlined, and to True in flow analysis to always
   --  analyze both the inlined code and the original subprogram, otherwise
   --  analysis may miss reads of uninitialized data due to the way inlining
   --  mechanism works.
   --
   --  Here is a case where a read of uninitialized data is missed when
   --  analyzing only the inlined code:
   --
   --     procedure Test2 (Done : out Boolean) is
   --     begin
   --        if Success then
   --           Done := ...;
   --        end if;
   --     end Test2;
   --
   --     procedure Test1 (I : Integer; Success : out Boolean) is
   --        Done : Boolean := False;
   --     begin
   --        Test2 (Done);
   --        Success := Success and Done;
   --     end Test1;
   --
   --  Here is a case where a read of uninitialized data is missed when
   --  analyzing only the original subprogram (and silencing flow analysis
   --  messages on the inlined code):
   --
   --     type R is record
   --        C : Integer;
   --     end record;
   --     X : R;
   --     procedure Local (Param : R) is
   --     begin
   --        Y := Param.C;
   --     end Local;
   --
   --     Local (X);

   function Full_Name (E : Entity_Id) return String
   with Pre => Nkind (E) in N_Entity;
   --  @param E any entity
   --  @return the name to use for E in Why3

   function Full_Name_Is_Not_Unique_Name (E : Entity_Id) return Boolean;
   --  In almost all cases, the name to use for an entity in Why3 is based on
   --  its unique name in GNAT AST, so that this name can be used everywhere
   --  to refer to the entity (for example to retrieve completion theories).
   --  A few cases require special handling because their name is predefined
   --  in Why3. This concerns currently only Standard_Boolean and its full
   --  subtypes and Universal_Fixed.
   --  @param E any entity
   --  @return True iff the name to use in Why3 (returned by Full_Name) does
   --     not correspond to unique name in GNAT AST.

   function Has_Volatile (E : Entity_Id) return Boolean;
   --  @param E an abstract state or object
   --  @return True iff E is an external state or a volatile object

   function Has_Volatile_Flavor
     (E : Entity_Id;
      A : Pragma_Id) return Boolean
   with Pre => Has_Volatile (E) and then
               Ekind (E) /= E_Constant and then
               A in Pragma_Async_Readers
                  | Pragma_Async_Writers
                  | Pragma_Effective_Reads
                  | Pragma_Effective_Writes;
   --  @param E an external state or a volatile object
   --  @return True iff E has the specified flavor A of volatility, either
   --     directly or through its type.

   function Is_Declared_In_Unit
     (E     : Entity_Id;
      Scope : Entity_Id) return Boolean;
   --  @param E any entity
   --  @param Scope scope
   --  @return True iff E is declared directly in Scope

   function Is_In_Analyzed_Files (E : Entity_Id) return Boolean
   with Pre => Present (E);
   --  @param E any entity
   --  @return True iff E is contained in a file that should be analyzed

   function Is_Not_Hidden_Discriminant (E : Entity_Id) return Boolean is
     (not (Ekind (E) = E_Discriminant and then Is_Completely_Hidden (E)));
   --  @param E any entity
   --  @return The opposite of Einfo.Is_Completely_Hidden
   --  Contrary to Einfo.Is_Completely_Hidden, this function can be called on
   --  any entity E, not only discriminants.

   function Is_Package_State (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E is an abstract state or a package level variable

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Loop_Parameter | E_Variable;
   --  @param E loop parameter
   --  @return True iff E has been introduced by a quantified expression

   function Source_Name (E : Entity_Id) return String
   with Pre => Nkind (E) in N_Has_Chars;
   --  @param E any entity
   --  @return The unscoped name of E as it appears in the source code;
   --          "" if E is equal to Empty.

   ------------------------------
   -- Queries related to types --
   ------------------------------

   function Check_Needed_On_Conversion (From, To : Entity_Id) return Boolean;
   --  @param From type of expression to be converted, which should be a Retysp
   --  @param To target type of the conversion, which should be a Retysp
   --  @return whether a check may be needed when converting an expression
   --     of type From to type To. Currently a very coarse approximation
   --     to rule out obvious cases.

   function Component_Is_Visible_In_SPARK (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Void | E_Component | E_Discriminant;
   --  @param E component
   --  @return True iff the component E should be visible in the translation
   --     into Why3, i.e. it is a discriminant (which cannot be hidden in
   --     SPARK) or the full view of the enclosing record is in SPARK.

   function Count_Non_Inherited_Discriminants
     (Assocs : List_Id) return Natural;
   --  @param Assocs list of component associations
   --  @return the number of discriminants used as choices in Assocs, ignoring
   --     those that are inherited from a parent type

   --  ??? Add a precondition to Count_Why_Regular_Fields and
   --  Count_Why_Top_Level_Fields that Retysp (E) = E ?

   function Count_Why_Regular_Fields (E : Entity_Id) return Natural;
   --  @param E record type or private type whose most underlying type is
   --     a record type. E should be a "Representative Type in SPARK".
   --  @return the number of regular fields in the record representing E into
   --     Why3, which contains:
   --     - A field per component of E visible in SPARK
   --       (use Component_Is_Visible_In_SPARK)
   --     - A field for the private part of E if E is a private type
   --     - A field for the extensions of E if E is tagged
   --     - A field for the private components of E's private ancestors if E is
   --       tagged and has private ancestors (use Has_Private_Ancestor_Or_Root)

   function Count_Why_Top_Level_Fields (E : Entity_Id) return Natural;
   --  @param E record type or private type whose most underlying type is
   --     a record type. E should be a "Representative Type in SPARK".
   --  @return the number of top-level fields in the record representing E into
   --     Why3, which contains:
   --     - A field __split_discrs for discriminants if E has at list one
   --     - A field __split_fields for regular fields if E has at list one
   --       (use Count_Why_Regular_Fields)
   --     - A field attr__constrained if E's discriminants have default values
   --     - A field __tag if E is tagged

   function Can_Be_Default_Initialized (Typ : Entity_Id) return Boolean is
     ((not Has_Array_Type (Typ) or else Is_Constrained (Typ))
      and then (not Has_Record_Type (Typ)
                or else not Has_Discriminants (Typ)
                or else Is_Constrained (Typ)
                or else Has_Defaulted_Discriminants (Typ))
      and then not Is_Class_Wide_Type (Typ));
   --  Determine wether there can be default initialized variables of a type.
   --  @param Typ any type
   --  @return False if Typ is unconstrained.

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
   --    Has_Default_Init_Cond and Has_Inherited_Default_Init_Cond for this
   --    type.
   --  @return the Default_Initialization_Kind of Typ

   function Get_Full_Type_Without_Checking (N : Node_Id) return Entity_Id
     with Pre => Present (N);
   --  Get the type of the given entity. This function looks through
   --  private types and should be used with extreme care.
   --  ??? This function should probably be removed. Its comment says it
   --  applies to entities, while it may be called from flow on entities or
   --  nodes of record type.

   function Get_Specific_Type_From_Classwide (E : Entity_Id) return Entity_Id
   with Pre => Is_Class_Wide_Type (E);
   --  Returns the specific type associated with a class wide type.
   --  If E's Etype is a fullview, returns its partial view instead.
   --  ??? This should make the mechanism with the extra table
   --  Specific_Tagged_Types redundant, except the detection that a type is
   --  a full view is currently not available soon enough.

   function Has_Private_Ancestor_Or_Root (E : Entity_Id) return Boolean;
   --  @param E any type
   --  @return True iff E is a tagged type whose translation into Why3 requires
   --     the use of an ancestor field, to denote invisible fieds from an
   --     ancestor at the Why3 level (due either to a private ancestor or
   --     a root type whose full view not in SPARK).

   function Has_Static_Discrete_Predicate (E : Entity_Id) return Boolean;
   --  @param E any type
   --  @return True iff E is a discrete type with a static predicate

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

   function Is_Static_Array_Type (E : Entity_Id) return Boolean;
   --  @param E any type
   --  @return True iff E is a constrained array type with statically known
   --     bounds

   function Nth_Index_Type (E : Entity_Id; Dim : Positive) return Node_Id
   with Pre => Is_Array_Type (E);
   --  @param E array type
   --  @param D dimension
   --  @return the argument E in the special case where E is a string literal
   --    subtype; otherwise the index type entity which corresponds to the
   --    selected dimension

   function Root_Record_Type (E : Entity_Id) return Entity_Id;
   --  Given a record type (or private type whose implementation is a record
   --  type, etc.), return the root type, including traversing private types.
   --  ??? Need to update comment to reflect dependence on Retysp of root by
   --  calling Full_View_Not_In_SPARK.

   function Root_Record_Component (E : Entity_Id) return Entity_Id;
   --  Given a component or discriminant of a record (sub-)type, return the
   --  corresponding component or discriminant of the root type, if any. This
   --  is the identity when E is the component of a root type.
   --  ??? Same update needed as for Root_Record_Type

   function Search_Component_By_Name
     (Rec  : Entity_Id;
      Comp : Entity_Id) return Entity_Id;
   --  Given a record type entity and a component/discriminant entity, search
   --  in Rec a component/discriminant entity with the same name. Returns Empty
   --  if no such component is found.

   function Is_Ancestor (Anc : Entity_Id; E : Entity_Id) return Boolean is
     (if not Is_Class_Wide_Type (Anc) then Sem_Type.Is_Ancestor (Anc, E)
      else Sem_Type.Is_Ancestor (Get_Specific_Type_From_Classwide (Anc), E));
   --  @param Anc A tagged type (which may or not be class-wide).
   --  @param E A tagged type (which may or not be class-wide).
   --  @result True if Anc is one of the ancestors of type E.

   function Static_Array_Length (E : Entity_Id; Dim : Positive) return Uint
   with Pre => Is_Static_Array_Type (E);
   --  @param E constrained array type with statically known bounds
   --  @param Dim dimension
   --  @return the static length of dimension Dim of E

   function Is_Protected_Component_Or_Discr (E : Entity_Id) return Boolean is
     (Ekind (E) in E_Component | E_Discriminant and then
      Ekind (Scope (E)) in Protected_Kind);
   --  @param E an entity
   --  @return True iff the entity is a component or discriminant of a
   --            protected type

   ------------------------------------
   -- Queries related to subprograms --
   ------------------------------------

   function Find_Contracts
     (E         : Entity_Id;
      Name      : Name_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Node_Lists.List
   with Pre => Ekind (E) in Subprogram_Kind | E_Package | E_Entry and then
               not (Classwide and Inherited);
   --  @param E subprogram or package
   --  @param Name contract name
   --  @param Classwide True when asking for the classwide version of contract
   --  @param Inherited True when asking only for inherited contracts
   --  @return the list of pragma nodes of E for contract Name

   function Get_Execution_Kind
     (E        : Entity_Id;
      After_GG : Boolean := True) return Execution_Kind_T
   with Pre  => Ekind (E) = E_Procedure,
        Post => Get_Execution_Kind'Result in Normal_Execution     |
                                             Abnormal_Termination |
                                             Infinite_Loop;
   --  @param E is a procedure that never returns, either marked with No_Return
   --     or for which flow analysis determines that no path returns.
   --  @param After_GG True if this call is made after generation of globals,
   --     so we can query the globals computed for E if not specified by the
   --     user.
   --  @return the kind of execution for E
   --
   --  Infer whether a call to E ends abnormally or loops infinitely. If a
   --  subprogram has an output, we assume that it contains an infinite loop.
   --  If it does not, we assume it is a thinly veiled wrapper around an
   --  exception raising program.
   --
   --  Certainly, if you have a procedure that never returns due to an
   --  exception, and it is implemented in SPARK, then you will run into
   --  trouble unless there is nothing of interest going on in it.
   --
   --  If we get this wrong, it is not the end of the world, as failure is
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

   function Get_Expression_Function (E : Entity_Id) return Node_Id;
   --  @param E subprogram
   --  @return if E is the entity for an expression function, return the
   --     corresponding N_Expression_Function original node. Otherwise,
   --     return Empty.

   function Get_Expr_From_Check_Only_Proc (E : Entity_Id) return Node_Id
     with Pre => Ekind (E) = E_Procedure;
   --  @param E procedure
   --  @return the expression in the first pragma Check found in the body of E,
   --     if any, or Empty otherwise
   --  Extract a condition being checked from a procedure intended to check
   --  this condition. This is used to extract the condition checked for aspect
   --  Default_Initialization.

   function Get_Expr_From_Return_Only_Func (E : Entity_Id) return Node_Id
     with Pre => Ekind (E) = E_Function;
   --  @param E procedure
   --  @return the expression in the first return statement found in the body
   --     of E, if any, or Empty otherwise
   --  Extract a condition being checked from a procedure intended to test
   --  this condition. This is used to extract the condition checked for aspect
   --  Dynamic_Predicate.

   function Has_Contracts
     (E         : Entity_Id;
      Name      : Name_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Boolean
   with Pre => Ekind (E) in Subprogram_Kind | E_Entry | E_Package;
   --  @param E subprogram or package
   --  @param Name contract name
   --  @param Classwide True when asking for the classwide version of contract
   --  @param Inherited True when asking only for inherited contracts
   --  @return True iff there is at least one contract Name for E

   function Has_Extensions_Visible (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in Subprogram_Kind | E_Entry;
   --  @param E subprogram
   --  @return True iff Extensions_Visible is specified for E

   function Has_User_Supplied_Globals (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in Subprogram_Kind | E_Entry;
   --  @param E subprogram
   --  @return True iff E has a data dependencies (Global) or flow
   --     dependencies (Depends) contract

   function Is_Error_Signaling_Procedure
     (E        : Entity_Id;
      After_GG : Boolean := True)
      return Boolean
   is
     (No_Return (E)
       and then Get_Execution_Kind (E, After_GG) = Abnormal_Termination);
   --  @param E subprogram
   --  @param After_GG is True when we can use the generated globals
   --  @return True iff E is marked No_Return and is considered to always
   --     terminate abnormally.

   function Is_Local_Subprogram_Always_Inlined (E : Entity_Id) return Boolean;
   --  @param E subprogram
   --  @return True iff E is a local subprogram that is always inlined by the
   --     frontend in GNATprove mode

   function Is_Requested_Subprogram_Or_Task (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E is a subprogram/task whose analysis was specifically
   --     requested, so it should be analyzed even if otherwise inlined

   function Is_Simple_Shift_Or_Rotate (E : Entity_Id) return Boolean;
   --  @param E subprogram
   --  @return True iff Subp is an intrisic shift or rotate for a modular type
   --     of modulus smaller or equal to 2 ** 64, with no functional contract
   --     (precondition, postcondition or contract cases).

   function Is_Unchecked_Conversion_Instance (E : Entity_Id) return Boolean;
   --  @param E subprogram
   --  @return True iff E is an instance of Ada.Unchecked_Conversion

   function Might_Be_Main (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in Subprogram_Kind | E_Subprogram_Body;
   --  @param E subprogram
   --  @return True iff E is a library level subprogram without formal
   --     parameters (E is allowed to have global parameters)

   function Subprogram_Full_Source_Name (E : Entity_Id) return String
     with Pre => Present (E) and then Sloc (E) /= No_Location;
   --  For a subprogram entity, return its scoped name, e.g. for subprogram
   --  Nested in
   --
   --    package body P is
   --       procedure Lib_Level is
   --          procedure Nested is
   --          ...
   --  return P.Lib_Level.Nested. Casing of names is taken as it appears in the
   --  source.
   --  @param E subprogram
   --  @return the fully scoped name of E as it appears in the source

   function Subprogram_Is_Ignored_For_Proof (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Function | E_Procedure | E_Task_Type | E_Entry;
   --  @param E subprogram
   --  @return True iff E should not be translated into Why3

   function Subp_Location (E : Entity_Id) return String
     with Pre => Ekind (E) in Subprogram_Kind |
                              E_Package       |
                              Task_Kind       |
                              Entry_Kind;
   --  @param E subprogram, package, task or entry
   --  @return a String of the form GP_Subp:foo.ads:12 pointing to the file and
   --    line where this entity is declared. This allows to identify the entity
   --    by its source position and is used e.g. for the --limit-subp switch of
   --    GNATprove.

   function Is_Protected_Subprogram (E : Entity_Id) return Boolean
   is (Ekind (E) = E_Entry or else
         (Ekind (E) in Subprogram_Kind and then
          Convention (E) = Convention_Protected));

   ------------------------------
   -- Queries related to tasks --
   ------------------------------

   function Task_Body (E : Entity_Id) return Node_Id
   with Pre  => Nkind (E) in N_Entity and then Ekind (E) = E_Task_Type,
        Post => (if Present (Task_Body'Result)
                 then Nkind (Task_Body'Result) = N_Task_Body);
   --  @param E task type
   --  @return the task body for the given type, similar to what
   --    Subprogram_Body might produce.

   function Task_Body_Entity (E : Entity_Id) return Entity_Id
   with Pre  => Nkind (E) in N_Entity and then Ekind (E) = E_Task_Type,
        Post => (if Present (Task_Body_Entity'Result)
                 then Ekind (Task_Body_Entity'Result) = E_Task_Body);
   --  @param E task type
   --  @return the entity of the task body for the given type, similar
   --    to what Subprogram_Body_Entity might produce.

   ------------------------------------------
   -- Queries related to protected objects --
   ------------------------------------------

   function PO_Body (E : Entity_Id) return Node_Id
   with Pre  => Nkind (E) in N_Entity and then Ekind (E) = E_Protected_Type,
        Post => (if Present (PO_Body'Result)
                 then Nkind (PO_Body'Result) = N_Protected_Body);
   --  @param E protected type
   --  @return the protected body for the given type, similar to what
   --    subprogram_body might produce.

   function PO_Definition (E : Entity_Id) return Node_Id
   with Pre  => Nkind (E) in N_Entity and then Ekind (E) = E_Protected_Type,
        Post => (if Present (PO_Definition'Result)
                 then Nkind (PO_Definition'Result) = N_Protected_Definition);
   --  @param E protected type
   --  @return the protected definition for the given type

   function Containing_Protected_Type (E : Entity_Id) return Entity_Id
     is (Scope (E))
     with Pre =>
             Ekind (E) in E_Function | E_Procedure | E_Entry
              | E_Component | E_Discriminant
             and (Is_Protected_Subprogram (E) or else
                  Ekind (Scope (E)) in Protected_Kind),
          Post => Ekind (Containing_Protected_Type'Result) in Protected_Kind;
   --  @param E a subprogram or entry or field which is part of a protected
   --            type
   --  @return the enclosing protected type

   --------------------------------
   -- Queries related to entries --
   --------------------------------

   function Entry_Body (E : Entity_Id) return Node_Id
   with Pre  => Nkind (E) in N_Entity and then
                Ekind (E) = E_Entry and then
                Nkind (Parent (E)) = N_Entry_Declaration,
        Post => (if Present (Entry_Body'Result)
                 then Nkind (Entry_Body'Result) = N_Entry_Body);
   --  @param E entry
   --  @return the entry body for the given entry, similar to what
   --    Subprogram_Body might produce.

   function Entry_Body_Entity (E : Entity_Id) return Node_Id
   with Pre  => Nkind (E) in N_Entity and then
                Ekind (E) = E_Entry and then
                Nkind (Parent (E)) = N_Entry_Declaration,
        Post => (if Present (Entry_Body_Entity'Result)
                 then Nkind (Entry_Body_Entity'Result) in N_Entity and then
                      Ekind (Entry_Body_Entity'Result) = E_Entry and then
                      Nkind (Parent (Entry_Body_Entity'Result)) =
                        N_Entry_Body);
   --  @param E entry
   --  @return the entry body entity for the given entry

   ---------------------------------
   -- Queries related to packages --
   ---------------------------------

   function In_Private_Declarations (Decl : Node_Id) return Boolean;
   --  @param Decl declaration node
   --  @return True iff Decl belongs to the list of private declarations of a
   --     package

   --------------------------------
   -- Queries related to pragmas --
   --------------------------------

   function Is_Pragma (N : Node_Id; Name : Pragma_Id) return Boolean;
   --  @param N any node
   --  @param Name pragma name
   --  @return True iff N is a pragma with the given Name

   function Is_Pragma_Annotate_GNATprove (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is a pragma Annotate (GNATprove, ...);

   function Is_Pragma_Check (N : Node_Id; Name : Name_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is a pragma Check (Name, ...);

   function Is_Ignored_Pragma_Check (N : Node_Id) return Boolean;
   --  @param N pragma
   --  @return True iff N is a pragma Check that can be ignored by analysis,
   --     because it is already taken into account elsewhere (precondition and
   --     postcondition, static predicate), or because it is completely ignored
   --     with a warning in SPARK.Definition (dynamic predicate).

   function Is_Pragma_Assert_And_Cut (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Pragma;
   --  @param N pragma
   --  @return True iff N is a pragma Assert_And_Cut

   procedure Get_Global_Items
     (P      :     Node_Id;
      Reads  : out Node_Sets.Set;
      Writes : out Node_Sets.Set);
   --  @param P pragma Global
   --  @param Reads inputs in P
   --  @param Writes outputs in P
   --  Computes the set of inputs and outputs in Global pragma P

   ---------------------------------
   -- Queries for arbitrary nodes --
   ---------------------------------

   function Body_File_Name (N : Node_Id) return String;
   --  @param N any node
   --  @return Same as [Spec_File_Name], but always return the file name of the
   --    body, if there is one.

   function In_Main_Unit (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is in the body or spec of the currently analyzed unit

   function In_Main_Unit_Body (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is in the body of the currently analyzed unit

   function In_Main_Unit_Spec (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is in the spec of the currently analyzed unit

   function Spec_File_Name (N : Node_Id) return String;
   --  @param N any node
   --  @return the name of the spec file of the unit which contains the node,
   --    if it exists, otherwise the body file. Also, we return the file name
   --    of the instance, not the generic.

   function Spec_File_Name_Without_Suffix (N : Node_Id) return String;
   --  @param any node
   --  @return same as Spec_File_Name but without the suffix.

   function String_Of_Node (N : Node_Id) return String;
   --  @param any expression node
   --  @return the node as pretty printed Ada code, limited to 50 chars

   function Get_Body (E : Entity_Id) return Node_Id
   with Pre  => Nkind (E) in N_Entity
                  and then Ekind (E) in E_Entry         |
                                        E_Task_Type     |
                                        Subprogram_Kind,
        Post => (if Present (Get_Body'Result)
                 then Nkind (Get_Body'Result) in N_Entry_Body      |
                                                 N_Subprogram_Body |
                                                 N_Task_Body);
   --  @param E is an entry, subprogram or task
   --  @return the body for the given entry/subprogram/task. This is a wrapper
   --    around Entry_Body, Subprogram_Body and Task_Body.

   function Get_Body_Entity (E : Entity_Id) return Entity_Id
   with Pre  => Nkind (E) in N_Entity and then
                Ekind (E) in E_Entry | E_Task_Type | Subprogram_Kind,
        Post => (if Present (Get_Body_Entity'Result)
                 then Ekind (Get_Body_Entity'Result) in E_Entry           |
                                                        E_Subprogram_Body |
                                                        E_Task_Body       |
                                                        Subprogram_Kind);
   --  @param E is an entry, subprogram or task
   --  @return the body entity for the given entry/subprogram/task.
   --    This is a wrapper around Entry_Body_Entity, Subprogram_Body_Entity
   --    and Task_Body_Entity.

   ----------------------------------
   -- Queries for particular nodes --
   ----------------------------------

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean;
   --  @param N aggregate or an extension aggregate
   --  @return True iff N is fully initialized. For the aggregate extension,
   --      this only deals with the extension components.

   function Get_Called_Entity (N : Node_Id) return Entity_Id
   with Pre  => Nkind (N) in N_Entry_Call_Statement | N_Subprogram_Call,
        Post => Nkind (Get_Called_Entity'Result) in N_Entity and then
                Ekind (Get_Called_Entity'Result) in E_Function  |
                                                    E_Procedure |
                                                    E_Entry;
   --  @param N a call statement
   --  @return the subprogram or entry called

   function Get_Formal_From_Actual (Actual : Node_Id) return Entity_Id
     with Pre => Nkind (Parent (Actual)) in N_Function_Call
                                          | N_Parameter_Association
                                          | N_Procedure_Call_Statement
                                          | N_Unchecked_Type_Conversion;
   --  @param Actual actual parameter of a call
   --  @return the corresponding formal parameter

   function Get_Range (N : Node_Id) return Node_Id
     with Post => Present (Low_Bound (Get_Range'Result)) and then
                  Present (High_Bound (Get_Range'Result));
   --  @param N more or less any node which has some kind of range, e.g. a
   --     scalar type entity or occurrence, a variable of such type, the type
   --     declaration or a subtype indication.
   --  @return the N_Range node of such a node

   function Is_Action (N : Node_Id) return Boolean
     with Pre => Nkind (N) = N_Object_Declaration;
   --  @param N is an object declaration
   --  @return if the given node N is an action

   function Is_Predicate_Function_Call (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is a call to a frontend-generated predicate function

   generic
      with procedure Handle_Argument (Formal, Actual : Node_Id);
   procedure Iterate_Call_Arguments (Call : Node_Id);
   --  Call [Handle_Argument] for each pair of formal and actual parameters
   --  of a function or procedure call.
   --  @param Call function or procedure call

   function Number_Of_Assocs_In_Expression (N : Node_Id) return Natural;
   --  @param N any node
   --  @return the number of N_Component_Association nodes in N.

   ---------------------------------
   -- Misc operations and queries --
   ---------------------------------

   procedure Append
     (To    : in out Node_Lists.List;
      Elmts : Node_Lists.List);
   --  Append all elements from list Elmts to the list To

   procedure Append
     (To    : in out Why_Node_Lists.List;
      Elmts : Why_Node_Lists.List);
   --  Append all elements from list Elmts to the list To

   function Unit_In_Standard_Library (U : Unit_Number_Type) return Boolean is
      (Get_Kind_Of_Unit (U) /= Not_Predefined_Unit);
   --  Returns True is unit U is in the standard library, which includes all
   --  units defined in Ada RM, and all units predefined by GNAT.

   function Location_In_Standard_Library (Loc : Source_Ptr) return Boolean;
   --  Returns True if location Loc is in a unit of the standard library, as
   --  computed by Unit_In_Standard_Library.

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
     (File_Name_Without_Suffix (Get_Name_String (Unit_File_Name (Main_Unit))));

   function File_Name (Loc : Source_Ptr) return String is
     (Get_Name_String (File_Name (Get_Source_File_Index (Loc))));
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

   function Has_Only_Nonblocking_Statements (N : Node_Id) return Boolean
     with Pre => Nkind (N) in N_Subprogram_Body | N_Entry_Body;
   --  Check if subprogram body N contains no potentially blocking statements

   function Is_Part_Of_Concurrent_Object (E : Entity_Id) return Boolean;
   --  Check if object E has Part_Of aspect that points to a concurrent object

end SPARK_Util;
