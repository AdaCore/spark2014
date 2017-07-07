------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            S P A R K _ U T I L                           --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                        Copyright (C) 2012-2017, AdaCore                  --
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

with Atree;             use Atree;
with Checked_Types;     use Checked_Types;
with Common_Containers; use Common_Containers;
with Einfo;             use Einfo;
with Impunit;           use Impunit;
with Lib;               use Lib;
with Namet;             use Namet;
with Nlists;            use Nlists;
with Sem_Util;          use Sem_Util;
with Sinfo;             use Sinfo;
with Sinput;            use Sinput;
with Snames;            use Snames;
with Types;             use Types;
with Urealp;            use Urealp;
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

   subtype Volatile_Pragma_Id is Pragma_Id with Static_Predicate =>
     Volatile_Pragma_Id in Pragma_Async_Readers
                         | Pragma_Async_Writers
                         | Pragma_Effective_Reads
                         | Pragma_Effective_Writes;
   --  A subtype for our special SPARK volatility aspects

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

   ---------------------------------
   -- Extra tables on expressions --
   ---------------------------------

   procedure Set_Dispatching_Contract (C, D : Node_Id);
   --  @param C expression of a classwide pre- or postcondition
   --  @param D dispatching expression for C, in which a reference to a
   --    controlling formal is interpreted as having the class-wide type. This
   --    is used to create a suitable pre- or postcondition expression for
   --    analyzing dispatching calls.

   function Dispatching_Contract (C : Node_Id) return Node_Id;
   --  @param C expression of a classwide pre- or postcondition
   --  @return the dispatching expression previously stored for C, or Empty if
   --    no such expression was stored for C.

   -----------------------------------------
   -- General queries related to entities --
   -----------------------------------------

   function Enclosing_Generic_Instance (E : Entity_Id) return Entity_Id
   with Post => (if Present (Enclosing_Generic_Instance'Result)
                 then Ekind (Enclosing_Generic_Instance'Result) = E_Package);
   --  @param E any entity
   --  @return entity of the enclosing generic instance package, if any

   function Enclosing_Unit (E : Entity_Id) return Entity_Id with
     Post => (if Present (Enclosing_Unit'Result)
              then Ekind (Enclosing_Unit'Result) in E_Function
                                                  | E_Procedure
                                                  | Entry_Kind
                                                  | E_Protected_Type
                                                  | E_Task_Type
                                                  | E_Package);
   --  Returns the entity of the package, subprogram, entry, protected object,
   --  or task enclosing E, if any. Returns Empty otherwise.

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

   function Full_Source_Name (E : Entity_Id) return String
     with Pre => Present (E) and then Nkind (E) in N_Has_Chars;
   --  Intented for use in debug output only
   --
   --  @param E any entity
   --  @return The qualified name of E as it appears in the source code, i.e.
   --          with "." as the scope separator.

   function Is_Declared_In_Unit
     (E     : Entity_Id;
      Scope : Entity_Id) return Boolean;
   --  @param E any entity
   --  @param Scope scope
   --  @return True iff E is declared directly in Scope

   function Is_In_Analyzed_Files (E : Entity_Id) return Boolean
     with Pre => Nkind (E) in N_Entity;
   --  Use this routine to ensure that the entity will be processed only by one
   --  invocation of gnat2why within a single pass of gnatprove. Technically,
   --  the "analyzed files" means either the spec alone or the spec and body.
   --
   --  @param E any entity
   --  @return True iff E is contained in a file that should be analyzed, i.e.
   --     in the spec file, the body file, or any file for a separate body
   --     declared in the body file.
   --
   --  Note: front end offers few similar, but subtly different queries, e.g.
   --  Entity_Is_In_Main_Unit (which is probably the most similar but returns
   --  False for the entity of the unit itself and crashes on Itypes),
   --  In_Extended_Main_Code_Unit (which returns True for entities in
   --  subunits), Sem_Ch12.Is_In_Main_Unit, Inline.In_Main_Unit_Or_Subunit
   --  (which do yet something else).

   function Source_Name (E : Entity_Id) return String
     with Pre => Nkind (E) in N_Has_Chars;
   --  @param E any entity
   --  @return The unqualified name of E as it appears in the source code;
   --          "" if E is equal to Empty.

   ----------------------------------------------
   -- Queries related to objects or components --
   ----------------------------------------------

   function Component_Is_Visible_In_SPARK (E : Entity_Id) return Boolean
     with Pre => Ekind (E) in E_Void | E_Component | E_Discriminant;
   --  @param E component
   --  @return True iff the component E should be visible in the translation
   --     into Why3, i.e. it is a discriminant (which cannot be hidden in
   --     SPARK) or the full view of the enclosing record is in SPARK.

   function Enclosing_Concurrent_Type (E : Entity_Id) return Entity_Id
   with Pre  => Is_Part_Of_Concurrent_Object (E) or else
                Is_Concurrent_Component_Or_Discr (E),
        Post => Ekind (Enclosing_Concurrent_Type'Result) in E_Protected_Type |
                                                            E_Task_Type;
   --  @param E is the entity of a component, discriminant or Part of
   --     concurrent type
   --  @return concurrent type

   function Has_Volatile (E : Checked_Entity_Id) return Boolean;
   --  @param E an abstract state or object
   --  @return True iff E is an external state or a volatile object

   function Has_Volatile_Flavor (E : Checked_Entity_Id;
                                 A : Volatile_Pragma_Id)
                                 return Boolean
   with Pre => Has_Volatile (E)
     and then Ekind (E) /= E_Constant;
   --  @param E an external state or a volatile object
   --  @return True iff E has the specified flavor A of volatility, either
   --     directly or through its type.

   function Is_Constant_After_Elaboration (E : Entity_Id) return Boolean
   with Pre => Ekind (E) = E_Variable;
   --  @param E entity of a variable
   --  @return True iff a Constant_After_Elaboration applies to E

   function Is_Concurrent_Component_Or_Discr (E : Entity_Id) return Boolean;
   --  @param E an entity
   --  @return True iff the entity is a component or discriminant of a
   --            concurrent type

   function Is_Global_Entity (E : Entity_Id) return Boolean;
   --  Returns True iff E represent an entity that can be a global

   function Is_Heap_Entity (E : Entity_Id) return Boolean renames No;
   --  Returns True iff E represens heap (which is in turn represented by an
   --  empty entity id and __HEAP entity name).

   function Is_Not_Hidden_Discriminant (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return Return True if E is not a Discriminant or if E is visible in
   --  SPARK.
   --  Contrary to Einfo.Is_Completely_Hidden, this function can be called on
   --  any entity E, not only discriminants.

   function Is_Package_State (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E is an abstract state or a package-level variable

   function Is_Part_Of_Concurrent_Object (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff the object has a Part_Of pragma that makes it part of a
   --    task or protected object.

   function Is_Part_Of_Protected_Object (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff the object has a Part_Of pragma that makes it part of a
   --    protected object.

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean
     with Pre => Ekind (E) in E_Loop_Parameter | E_Variable;
   --  @param E loop parameter
   --  @return True iff E has been introduced by a quantified expression

   function Is_Protected_Component_Or_Discr (E : Entity_Id) return Boolean;
   --  @param E an entity
   --  @return True iff the entity is a component or discriminant of a
   --            protected type

   function Is_Protected_Component_Or_Discr_Or_Part_Of
     (E : Entity_Id) return Boolean
   is (Is_Protected_Component_Or_Discr (E) or else
       Is_Part_Of_Protected_Object (E));
   --  @param E an entity
   --  @return True iff E is logically part of a protected object, either being
   --    a discriminant of field of the object, or being a "part_of".

   function Is_Synchronized (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Abstract_State |
                            E_Protected_Type |
                            E_Task_Type      |
                            Object_Kind;
   --  @param E an entity that represents a global
   --  @return True if E is safe to be accesses from multiple tasks

   function Root_Record_Component (E : Entity_Id) return Entity_Id;
   --  Given a component or discriminant of a record (sub-)type, return the
   --  corresponding component or discriminant of the root type, if any. This
   --  is the identity when E is the component of a root type.
   --  ??? Same update needed as for Root_Record_Type

   function Search_Component_By_Name
     (Rec  : Entity_Id;
      Comp : Entity_Id) return Entity_Id;
   --  Given a record type entity and a component/discriminant entity, search
   --  in Rec a component/discriminant entity with the same name and the same
   --  original record component. Returns Empty if no such component is found.
   --  In particular returns empty on hidden components.

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

   ---------------------------------
   -- Queries for arbitrary nodes --
   ---------------------------------

   function Body_File_Name (N : Node_Id) return String;
   --  @param N any node
   --  @return Same as [Spec_File_Name], but always return the file name of the
   --    body, if there is one.

   function In_Internal_Unit (N : Node_Or_Entity_Id) return Boolean;
   --  Returns True if the given node or entity appears within the source text
   --  of an internal unit (i.e. within Ada, GNAT, Interfaces, System or within
   --  one of the descendant packages of one of these four packages).
   --
   --  Note: this routine is based on In_Predefined_Unit from the front end,
   --  but also detected nodes for the GNAT package.

   function In_Internal_Unit (S : Source_Ptr) return Boolean;
   --  Same function as above but argument is a source pointer

   function Spec_File_Name (N : Node_Id) return String;
   --  @param N any node
   --  @return the name of the spec file of the unit which contains the node,
   --    if it exists, otherwise the body file. Also, we return the file name
   --    of the instance, not the generic.

   function Spec_File_Name_Without_Suffix (N : Node_Id) return String;
   --  @param N any node
   --  @return same as Spec_File_Name but without the suffix.

   function String_Of_Node (N : Node_Id) return String;
   --  @param N any expression node
   --  @return the node as pretty printed Ada code, limited to 50 chars

   ----------------------------------
   -- Queries for particular nodes --
   ----------------------------------

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean;
   --  @param N aggregate or an extension aggregate
   --  @return True iff N is fully initialized. For the aggregate extension,
   --      this only deals with the extension components.

   function Full_Entry_Name (N : Node_Id) return String
     with Pre => Nkind (N) in N_Selected_Component
                            | N_Expanded_Name
                            | N_Indexed_Component
                            | N_Defining_Identifier
                            | N_Identifier;
   --  @param N is a component of the whole prefix for an entry call
   --  @return the full name for an entry call

   function Generic_Actual_Subprograms (E : Entity_Id) return Node_Sets.Set
   with Pre  => Is_Generic_Instance (E),
        Post => (for all S of Generic_Actual_Subprograms'Result =>
                    Is_Subprogram (S));
   --  @param E instance of a generic unit
   --  @return actual subprogram parameters of E

   function Get_Called_Entity (N : Node_Id) return Entity_Id
     with Pre  => Nkind (N) in N_Entry_Call_Statement | N_Subprogram_Call,
          Post => Nkind (Get_Called_Entity'Result) in N_Entity and then
                  Ekind (Get_Called_Entity'Result) in E_Function  |
                                                      E_Procedure |
                                                      Entry_Kind;
   --  @param N a call statement
   --  @return the subprogram or entry called
   --  ??? this duplicates a private function front end Get_Function_Id
   --      (which perhaps should be renamed to Get_Subprogram_Id, since it
   --       is explicitly used also for procedures and entries)

   function Get_Formal_From_Actual (Actual : Node_Id) return Entity_Id
     with Pre  => Nkind (Parent (Actual)) in N_Function_Call            |
                                             N_Parameter_Association    |
                                             N_Procedure_Call_Statement |
                                             N_Entry_Call_Statement     |
                                             N_Unchecked_Type_Conversion,
          Post => Present (Get_Formal_From_Actual'Result);
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

   function Is_Converted_Actual_Output_Parameter (N : Node_Id) return Boolean;
   --  @param N expression
   --  @return True iff N is either directly an out or in out actual parameter,
   --     or under one or multiple type conversions, where the most enclosing
   --     type conversion is an out or in out actual parameter.

   function Is_Call_Arg_To_Predicate_Function (N : Node_Id) return Boolean;
   --  @param N expression node or Empty
   --  @return True iff N is the argument to a call to a frontend-generated
   --     predicate function. This should only occur when analyzing the code
   --     for the predicate function of a derived type, so the argument
   --     should take the form of a type conversion. Node N should be the
   --     expression being converted rather than the type conversion itself.

   function Is_Empty_Others (N : Node_Id) return Boolean
     with Pre  => Nkind (N) = N_Case_Statement_Alternative,
          Post => (if Is_Empty_Others'Result
                   then No (Next (N)) and then
                        List_Length (Discrete_Choices (N)) = 1);
   --  Returns True iff N is an "others" case alternative with empty set
   --  of discrite choices (this set is statically determined by the front
   --  end). Such an alternative must not be followed by other alternatives
   --  and "others" must be its only choice.

   function Is_External_Call (N : Node_Id) return Boolean
   with Pre => Nkind (N) in N_Entry_Call_Statement | N_Subprogram_Call
                 and then
               Within_Protected_Type (Get_Called_Entity (N));
   --  @param N call node
   --  @return True iff N is an external call to a protected subprogram or
   --     a protected entry.
   --
   --  Note: calls to protected functions in preconditions and guards of the
   --  Contract_Cases are external, but this routine treats them as internal.
   --  However, this only matters for marking where such a calls are rejected
   --  anyway; for flow and proof this routine gives correct results.

   function Is_Predicate_Function_Call (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is a call to a frontend-generated predicate function

   generic
      with procedure Handle_Parameter (Formal : Entity_Id; Actual : Node_Id);
   procedure Iterate_Call_Parameters (Call : Node_Id)
   with Pre => Nkind (Call) in N_Subprogram_Call | N_Entry_Call_Statement;
   --  Call [Handle_Parameter] for each pair of formal and actual parameters
   --  of a function or procedure call.
   --  @param Call function or procedure call

   generic
      with procedure Handle_Parameters (Formal : Node_Id; Actual : Node_Id);
   procedure Iterate_Generic_Parameters (E : Entity_Id)
   with Pre => Ekind (E) = E_Package;
   --  Call [Handle_Parameters] for each generic formal and actual parameter of
   --  a generic instance.
   --  @param E represents the entity of the instantiated generic package. For
   --  subprogram instances this is the wrapper package obtained after
   --  expansion.

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

   function Char_To_String_Representation (C : Character) return String;
   --  @param C a character to print in a counterexample
   --  @return a string representing the character for humans to read, which is
   --     the character itself if it is a graphic one, otherwise its name.

   function Unit_In_Standard_Library (U : Unit_Number_Type) return Boolean is
     (Get_Kind_Of_Unit (U) /= Not_Predefined_Unit);
   --  Returns True is unit U is in the standard library, which includes all
   --  units defined in Ada RM, and all units predefined by GNAT.

   function Location_In_Standard_Library (Loc : Source_Ptr) return Boolean;
   --  Returns True if location Loc is in a unit of the standard library, as
   --  computed by Unit_In_Standard_Library.

   function Get_Flat_Statement_And_Declaration_List
     (Stmts : List_Id) return Node_Lists.List;
   --  Given a list of statements and declarations Stmts, returns the flattened
   --  list that includes these statements and declarations, and recursively
   --  all inner declarations and statements that appear in block statements.

   function Is_Others_Choice (Choices : List_Id) return Boolean;
   --  Returns True if Choices is the singleton list with an "others" element

   function File_Name_Without_Suffix (File_Name : String) return String;

   function Real_Image (U : Ureal; Max_Length : Integer) return String;
   --  Return a string, of maximum length Max_length, representing U.

   function String_Value (Str_Id : String_Id) return String;

   function Unit_Name return String is
     (File_Name_Without_Suffix (Get_Name_String (Unit_File_Name (Main_Unit))));

   function File_Name (Loc : Source_Ptr) return String is
     (Get_Name_String (File_Name (Get_Source_File_Index (Loc))));
   --  @param Loc any source pointer
   --  @return the file name of the source pointer (will return the file of the
   --    generic in case of instances)

   function Safe_First_Sloc (N : Node_Id) return Source_Ptr;
   --  Wrapper for First_Sloc that is safe to use for nodes coming from
   --  instances of generic units and subprograms inlined for proof.
   --
   --  ??? this is only a temporary fix and should be removed once the
   --  underlying problem with First_Sloc is fixed.

end SPARK_Util;
