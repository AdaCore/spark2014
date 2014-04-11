------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            S P A R K _ U T I L                           --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                        Copyright (C) 2012-2014, AdaCore                  --
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

with Atree;            use Atree;
with Einfo;            use Einfo;
with Impunit;          use Impunit;
with Namet;            use Namet;
with Sinfo;            use Sinfo;
with Snames;           use Snames;
with Types;            use Types;

with Why.Atree.Tables; use Why.Atree.Tables;

with Common_Containers; use Common_Containers;

package SPARK_Util is

   -------------------
   -- Special Names --
   -------------------

   Name_GNATprove : constant String := "gnatprove";
   Name_External_Axiomatization : constant String := "external_axiomatization";

   ------------------------------
   -- Queries on Type Entities --
   ------------------------------

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
     (Typ : Entity_Id) return Default_Initialization_Kind;
   --  Determine default initialization kind that applies to a particular
   --  type. Types defined in axiomatized units (such as formal containers) and
   --  private types are treated specially, so that they are either considered
   --  as having full default initialized, or no default initialization.

   function Is_Initialized_By_Formal_Container (N : Node_Id) return Boolean;
   --  Returns true if the type of the corresponding entity appears within
   --  the source text of a predefined unit (i.e. within Ada, Interfaces,
   --  System or within one of the descendent packages of one of these three
   --  packages) and is considered to be default initialized because it is
   --  declared in a formal container.
   --
   --  ??? This should be removed once N122-014 is implemented.

   ---------------
   -- Utilities --
   ---------------

   function Lowercase_Has_Element_Name return String;
   --  Return the name of the function Has_Element in formal containers

   function Lowercase_Iterate_Name return String;
   --  Return the name of the function Iterate in formal containers

   function Lowercase_Capacity_Name return String;
   --  Return the name of the discriminant Capacity in formal containers

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean;
   --  Return whether aggregate N is fully initialized

   function All_Aggregates_Are_Fully_Initialized
     (N : Node_Id) return Boolean;
   --  Return whether all aggregates in node N (recursively) are fully
   --  initialized.

   function Get_Enclosing_Declaration (N : Node_Id) return Node_Id;
   --  Return the declaration node enclosing N, if any, by following the chain
   --  of Parent's links.

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

   function Get_Subprogram_Contract_Cases (E : Entity_Id) return Node_Id;
   --  Return the pragma Contract_Cases for E, if any

   function Expression_Functions_All_The_Way (E : Entity_Id) return Boolean;
   --  Given the entity E for a function, determine whether E is an expression
   --  function that only calls expression functions, directly or indirectly.

   procedure Add_Full_And_Partial_View (Full, Partial : Entity_Id);
   --  Store the correspondance between the Full and Partial views of the same
   --  entity, for deferred constants and private types.

   function In_Private_Declarations (Decl : Node_Id) return Boolean;
   --  Returns whether Decl belongs to the list of private declarations of a
   --  package.

   function Is_Full_View (E : Entity_Id) return Boolean;
   --  Return whether E is the full view of another entity

   function Is_Partial_View (E : Entity_Id) return Boolean;
   --  Return whether E is the partial view of another entity

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

   function Package_Has_External_Axioms (E : Entity_Id) return Boolean with
     Pre  => Ekind_In (E, E_Package, E_Generic_Package);
   --  Return whether E is a package with External Axioms

   function Type_Based_On_External_Axioms (E : Entity_Id) return Boolean;
   --  Return whether a private type E is defined in the private part of a
   --  package with external axioms, or it is a subtype or derived type
   --  ultimately based on such a type.

   function Entity_In_External_Axioms (E : Entity_Id) return Boolean;
   --  Return whether an entity E is declared in a package with external axioms

   function Underlying_External_Axioms_Type (E : Entity_Id) return Entity_Id;
   --  Return the underlying (private) base type declared in a package with
   --  external axioms of a private type E, if any

   function Axiomatized_Package_For_Entity (E : Entity_Id) return Entity_Id;
   --  Returns the package entity with an external axiomatization containing E,
   --  if any, or Empty if none.

   function Is_External_Axioms_Discriminant (E : Entity_Id) return Boolean
   with
     Pre => Ekind (E) = E_Discriminant;

   function Is_Access_To_External_Axioms_Discriminant
     (N : Node_Id) return Boolean
   with
     Pre => Nkind (N) = N_Selected_Component;

   function Partial_View (E : Entity_Id) return Entity_Id;
   --  Return the partial view for entity E

   function Unit_In_Standard_Library (U : Unit_Number_Type) return Boolean is
      (Get_Kind_Of_Unit (U) /= Not_Predefined_Unit);
   --  Returns True is unit U is in the standard library, which includes all
   --  units defined in Ada RM, and all units predefined by GNAT.

   function Location_In_Standard_Library (Loc : Source_Ptr) return Boolean;
   --  Returns True if location Loc is in a unit of the standard library, as
   --  computed by Unit_In_Standard_Library.

   function Root_Record_Type (E : Entity_Id) return Entity_Id;
   --  Given a record type (or private type whose implementation is a record
   --  type, etc.), return the root type, including traversing private types.

   function Root_Record_Component (E : Entity_Id) return Entity_Id;
   --  Given a component or discriminant of a record (sub-)type, return the
   --  corresponding component or discriminant of the root type. This is the
   --  identity when E is the component of a root type.

   function Search_Component_By_Name
     (Rec  : Entity_Id;
      Comp : Entity_Id) return Entity_Id;
   --  Given a record type entity and a component/discriminant entity, search
   --  in Rec a component/discriminant entity with the same name. The caller of
   --  this function should be sure that there is such a component, because it
   --  raises Program_Error if it doesn't find any.

   function Matching_Component_Association
     (Component   : Entity_Id;
      Association : Node_Id) return Boolean;
   --  Return whether Association matches Component

   function Number_Components (Typ : Entity_Id) return Natural;
   --  Count the number of components in record type Typ

   function First_Discriminant (Id : E) return E
     with Pre =>
       (Is_Record_Type (Id) or else Is_Incomplete_Or_Private_Type (Id));
   --  Get the first discriminant of the record type entity [Id]

   procedure Append
     (To    : in out List_Of_Nodes.List;
      Elmts : List_Of_Nodes.List);
   --  Append all elements from list Elmts to the list To

   procedure Append
     (To    : in out Node_Lists.List;
      Elmts : Node_Lists.List);
   --  Append all elements from list Elmts to the list To

   function Get_Statement_And_Declaration_List
     (Stmts : List_Id) return List_Of_Nodes.List;
   --  Given a list of statements and declarations Stmts, returns the same list
   --  seen as a container list of nodes.

   function Get_Flat_Statement_And_Declaration_List
     (Stmts : List_Id) return List_Of_Nodes.List;
   --  Given a list of statements and declarations Stmts, returns the flattened
   --  list that includes these statements and declarations, and recursively
   --  all inner declarations and statements that appear in block statements.

   function Is_Pragma (N : Node_Id; Name : Pragma_Id) return Boolean;
   --  Returns whether N is a pragma of the given kind

   function Is_Pragma_Check (N : Node_Id; Name : Name_Id) return Boolean;
   --  Returns whether N has the form pragma Check (Name, ...)

   function Innermost_Enclosing_Loop (N : Node_Id) return Node_Id;
   --  Returns the innermost loop enclosing N, if any, and Empty otherwise

   function Is_Toplevel_Entity (E : Entity_Id) return Boolean;
   --  Returns True if E is a toplevel entity, only enclosed in package specs
   --  or in the declaration part of package bodies.

   function Is_Unchecked_Conversion_Instance (E : Entity_Id) return Boolean;
   --  Returns whether E is an instance of Ada.Unchecked_Conversion

   function Is_Annotate_Pragma_For_External_Axiomatization
     (N : Node_Id) return Boolean;
   --  Returns whether N is
   --    pragma Annotate (GNATprove, External_Axiomatization);

   function Has_Annotate_Pragma_For_External_Axiomatization
     (E : Entity_Id) return Boolean
   with Pre => Ekind_In (E, E_Package, E_Generic_Package);
   --  Returns whether E is a package entity, for which the initial list of
   --  pragmas at the start of the package declaration contains
   --    pragma Annotate (GNATprove, External_Axiomatization);

   procedure Get_Global_Items
     (P      : Node_Id;
      Reads  : out Node_Sets.Set;
      Writes : out Node_Sets.Set);
   --  Returns the set of input and output items in Global pragma P

   function Get_Formal_Type_From_Actual (Actual : Node_Id) return Entity_Id
   with
     Pre => Nkind_In (Parent (Actual), N_Function_Call,
                                       N_Parameter_Association,
                                       N_Procedure_Call_Statement);
   --  Given an actual parameter Actual of a call, returns the type of the
   --  corresponding formal parameter.

   function Check_Needed_On_Conversion (From, To : Entity_Id) return Boolean;
   --  Returns whether a check may be needed when converting an expression
   --  of type From to an expression of type To. Currently a very coarse
   --  approximation to rule out obvious cases.

   function Is_Others_Choice (Choices : List_Id) return Boolean;
   --  Returns True if Choices is the singleton list with an "others" element

   function Is_Standard_Boolean_Type (N : Node_Id) return Boolean;
   --  Returns True if N is a sybtype of Standard_Boolean with the same
   --  Scalar_Range

   function Analysis_Requested (E : Entity_Id) return Boolean;
   --  Returns true if entity E has to be analyzed.

   function Get_Cursor_Type_In_Iterable_Aspect
     (Typ : Entity_Id) return Entity_Id;
   --  Returns the cursor type implied by an Iterable aspect over the type Typ

   function Get_Element_Type_In_Iterable_Aspect
     (Typ : Entity_Id) return Entity_Id;
   --  Returns the element type implied by an Iterable aspect over the type Typ

   function Is_Local_Subprogram_Always_Inlined (E : Entity_Id) return Boolean;
   --  Returns True if E is a local subprogram that is always inlined by the
   --  frontend in GNATprove mode.

end SPARK_Util;
