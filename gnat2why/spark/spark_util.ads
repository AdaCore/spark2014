------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            S P A R K _ U T I L                           --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2012-2019, AdaCore                     --
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

with Assumption_Types;  use Assumption_Types;
with Atree;             use Atree;
with Checked_Types;     use Checked_Types;
with Common_Containers; use Common_Containers;
with Einfo;             use Einfo;
with Lib;               use Lib;
with Namet;             use Namet;
with Nlists;            use Nlists;
with Sem_Aux;           use Sem_Aux;
with Sem_Util;          use Sem_Util;
with Sinfo;             use Sinfo;
with Sinput;            use Sinput;
with Snames;            use Snames;
with Types;             use Types;
with Uintp;             use Uintp;
with Urealp;            use Urealp;
with Why.Atree.Tables;  use Why.Atree.Tables;

package SPARK_Util is

   ---------------------------------------------------
   --  Utility types related to entities and nodes  --
   ---------------------------------------------------

   subtype N_Ignored_In_SPARK is Node_Kind with
     Predicate =>
       N_Ignored_In_SPARK in
           N_Call_Marker
         | N_Exception_Declaration
         | N_Freeze_Entity
         | N_Freeze_Generic_Entity
         | N_Implicit_Label_Declaration
         | N_Incomplete_Type_Declaration
         | N_Itype_Reference
         | N_Label
         | N_Null_Statement
         | N_Number_Declaration

         --  Renamings are replaced by the renamed object in the frontend, but
         --  the renaming objects are not removed from the tree. We can safely
         --  ignore them.

         | N_Renaming_Declaration

         --  Generic instantiations are expanded into the corresponding
         --  declarations in the frontend. The instantiations themselves can be
         --  ignored.

         | N_Package_Instantiation
         | N_Subprogram_Instantiation
         | N_Use_Package_Clause
         | N_Use_Type_Clause
         | N_Validate_Unchecked_Conversion
         | N_Variable_Reference_Marker;

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

   type Scalar_Check_Kind is
     (RCK_Overflow,
      RCK_FP_Overflow,
      RCK_Range,
      RCK_Length,
      RCK_Index,
      RCK_Range_Not_First,
      RCK_Range_Not_Last,
      RCK_Overflow_Not_First,
      RCK_Overflow_Not_Last);
   --  Kind for checks on scalar types

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
   --  @param E any entity
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

   function Canonical_Entity
     (Ref     : Entity_Id;
      Context : Entity_Id)
      return Entity_Id
   with Pre => Ekind (Context) in Entry_Kind
                                | E_Function
                                | E_Package
                                | E_Procedure
                                | E_Protected_Type
                                | E_Task_Type
                                | Record_Kind
                                | Private_Kind;
   --  Subsidiary to the parsing of flow contracts, i.e. [Refined_]Depends,
   --  [Refined_] Global and Initializes, and default expressions.
   --
   --  If entity Ref denotes the current instance of a concurrent type, as seen
   --  from Context, then returns the entity of that concurrent type;
   --  otherwise, returns Unique_Entity of E.
   --
   --  Note: this routine converts references to the current instance of a
   --  concurrent type within a single concurrent unit from E_Variable (which
   --  is more convenient for the frontend) to the type entity (which is more
   --  convenient to the SPARK backend).

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
     Post => Ekind (Enclosing_Unit'Result) in E_Function
                                            | E_Procedure
                                            | Entry_Kind
                                            | E_Protected_Type
                                            | E_Task_Type
                                            | E_Package;
   --  Returns the entity of the package, subprogram, entry, protected type,
   --  or task type enclosing E.

   function Directly_Enclosing_Subprogram_Or_Entry
     (E : Entity_Id) return Entity_Id;
   --  Returns the entity of the first subprogram or entry enclosing E. Returns
   --  Empty if there is no such subprogram or if something else than a package
   --  (a concurrent type or a block statement) is encountered while going up
   --  the scope of E

   function Entity_Comes_From_Source (E : Entity_Id) return Boolean is
      (Comes_From_Source (E)
        or else Comes_From_Source (Atree.Parent (E)))
   with Pre => Nkind (E) in N_Entity;
   --  Ideally we should only look at whether entity E comes from source,
   --  but in various cases this is not properly set in the frontend (for
   --  subprogram inlining and generic instantiations), which cannot be fixed
   --  easily. So we also look at whether the parent node comes from source,
   --  which is more often correct.

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
     with Pre => Present (E) and then Sloc (E) /= No_Location;
   --  For an entity E, return its scoped name, e.g. for a subprogram
   --  nested in
   --
   --    package body P is
   --       procedure Lib_Level is
   --          procedure Nested is
   --          ...
   --  return P.Lib_Level.Nested. Casing of names is taken as it appears in the
   --  source.
   --  @param E an entity
   --  @return the fully scoped name of E as it appears in the source

   function Is_Declared_In_Unit
     (E     : Entity_Id;
      Scope : Entity_Id) return Boolean;
   --  @param E any entity
   --  @param Scope scope
   --  @return True iff E is declared directly in Scope

   function Is_Declared_In_Main_Lib_Unit (N : Node_Id) return Boolean;
   --  @param any entity Node which is not in Standard
   --  @return True iff E is declared in the same library unit as the analysed
   --      unit. Go from child packages to parents for comparison.

   function Is_Declared_In_Private (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E is declared in the private part of a package

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
     with Pre => Present (E) and then Nkind (E) in N_Has_Chars;
   --  @param E any entity
   --  @return The unqualified name of E as it appears in the source code

   ----------------------------------------------
   -- Queries related to objects or components --
   ----------------------------------------------

   function Component_Is_Visible_In_SPARK (E : Entity_Id) return Boolean
     with Pre => Ekind (E) in E_Component | E_Discriminant;
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

   function Has_Volatile (E : Checked_Entity_Id) return Boolean
   with Pre  => Ekind (E) in E_Abstract_State
                           | E_Protected_Type
                           | E_Task_Type
                           | Object_Kind,
        Post => (if Ekind (E) in E_Protected_Type | E_Task_Type
                 then not Has_Volatile'Result);
   --  @param E an abstract state or object (including concurrent types, which
   --     might be implicit parameters and globals)
   --  @return True iff E is an external state or a volatile object

   function Has_Volatile_Property (E : Checked_Entity_Id;
                                   P : Volatile_Pragma_Id)
                                 return Boolean
   with Pre => Has_Volatile (E)
     and then Ekind (E) /= E_Constant;
   --  @param E an external state, a volatile object, or a protected component
   --  @return True iff E has the specified property P of volatility, either
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

   function Is_Not_Hidden_Discriminant (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return Return True if E is not a Discriminant or if E is visible in
   --  SPARK.
   --  Contrary to Einfo.Is_Completely_Hidden, this function can be called on
   --  any entity E, not only discriminants.

   function Is_Package_State (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E can appear on the LHS of an Initializes contract

   function Is_Part_Of_Concurrent_Object (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff the object has a Part_Of pragma that makes it part of a
   --    task or protected object.

   function Is_Part_Of_Protected_Object (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff the object has a Part_Of pragma that makes it part of a
   --    protected object.

   function Is_Predefined_Initialized_Entity (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True if E is predefined and initialized variable (see below)
   --
   --  Note: this function, as it is implemented now, may fail to recognize
   --  some variables as initialized, but this is acceptable (i.e. this will
   --  only cause false alarms and not missing checks). If this happens, then
   --  the implementation should be improved to match the spec.

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

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean
     with Pre => Ekind (E) in E_Loop_Parameter | E_Variable;
   --  @param E loop parameter
   --  @return True iff E has been introduced by a quantified expression

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
   --  ??? Same update needed as for Root_Retysp

   function Search_Component_By_Name
     (Rec  : Entity_Id;
      Comp : Entity_Id) return Entity_Id;
   --  Given a record type entity and a component/discriminant entity, search
   --  in Rec a component/discriminant entity with the same name and the same
   --  original record component. Returns Empty if no such component is found.
   --  In particular returns empty on hidden components.

   function Is_Local_Borrower (E : Entity_Id) return Boolean;
   --  Return True is E is a constant or a variable of an anonymous access to
   --  variable type.

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

   function Declaration_Is_Associated_To_Parameter
     (N : Node_Id) return Boolean
     with Pre => Present (N);
   --  @param N any node
   --  return True if N has a Related_Expression attribute associated to
   --  a parameter entity.
   --  Declarations associated to subprogram parameters are translated before
   --  the precondition so that checks related to parameters can be discharged
   --  when verifying the precondition itself.

   generic
      with function Property (N : Node_Id) return Boolean;
   function First_Parent_With_Property (N : Node_Id) return Node_Id with
     Post => No (First_Parent_With_Property'Result)
     or else Property (First_Parent_With_Property'Result);
   --  @param N any node
   --  @return the first node in the chain of parents of N for which Property
   --     returns True.

   function Get_Initialized_Object (N : Node_Id) return Entity_Id with
     Pre  => Nkind (N) in N_Subexpr,
     Post => No (Get_Initialized_Object'Result)
     or else Is_Object (Get_Initialized_Object'Result);
   --  @param N any expression node
   --  @return if N is used to initialize an object, return this object. Return
   --      Empty otherwise. This is used to get a stable name for aggregates
   --      used as definition of objects.

   function Is_In_Statically_Dead_Branch (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True if the node is in a branch that is statically dead. Only
   --      if-statements are detected for now.

   function May_Issue_Warning_On_Node (N : Node_Id) return Boolean;
   --  We do not issue any warnings on nodes which stem from inlining or
   --  instantiation, or in subprograms or library packages whose analysis
   --  has not been requested, such as subprograms that are always inlined
   --  in proof.

   function Shape_Of_Node (Node : Node_Id) return String;
   --  Return a string representing the shape of the Ada code surrounding the
   --  input node. This is used to name the VC file for manual proof.

   ----------------------------------
   -- Queries for particular nodes --
   ----------------------------------

   type Unrolling_Type is
     (No_Unrolling,
      Simple_Unrolling,
      --  body of the loop repeated N times
      Unrolling_With_Condition
      --  value used for unrolling with a condition to check loop test, which
      --  is necessary when the loop has a dynamic range
     );

   function Is_Selected_For_Loop_Unrolling
     (Loop_Stmt : Node_Id) return Boolean;
   --  Return whether [Loop_Stmt] is unrolled or not

   procedure Candidate_For_Loop_Unrolling
     (Loop_Stmt   : Node_Id;
      Output_Info : Boolean;
      Result      : out Unrolling_Type;
      Low_Val     : out Uint;
      High_Val    : out Uint)
   with Pre => Nkind (Loop_Stmt) = N_Loop_Statement;
   --  @param Output_Info whether the reason for not unrolling should be
   --         displayed when the loop has no loop invariant, and a positive
   --         message that the loop is unrolled when applicable.
   --  @param Result whether a loop is a candidate for loop unrolling
   --  @param Low_Val the loop bound for loop unrolling
   --  @param High_Val the high bound for loop unrolling

   function Full_Entry_Name (N : Node_Id) return String
     with Pre => Nkind (N) in N_Expanded_Name
                            | N_Identifier
                            | N_Indexed_Component
                            | N_Selected_Component;
   --  @param N is a prefix of an entry call; it denotes either a stand-alone
   --     protected object or a protected component within a composite object
   --  @return a name that uniquely identifies the prefix

   function Generic_Actual_Subprograms (E : Entity_Id) return Node_Sets.Set
   with Pre  => Is_Generic_Instance (E),
        Post => (for all S of Generic_Actual_Subprograms'Result =>
                    Is_Subprogram (S));
   --  @param E instance of a generic unit
   --  @return actual subprogram parameters of E

   function Get_Formal_From_Actual (Actual : Node_Id) return Entity_Id
     with Pre  => Nkind (Parent (Actual)) in N_Subprogram_Call          |
                                             N_Entry_Call_Statement     |
                                             N_Parameter_Association    |
                                             N_Unchecked_Type_Conversion,
          Post => Is_Formal (Get_Formal_From_Actual'Result);
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

   function Is_Error_Signaling_Statement (N : Node_Id) return Boolean;
   --  Returns True iff N is a statement used to signal an error:
   --    . a raise statement
   --    . a pragma Assert (False)
   --    . a call to an error-signaling procedure

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
   --  However, the front end rejects these two cases. For the SPARK back end,
   --  this routine gives correct results.

   function Is_Predicate_Function_Call (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is a call to a frontend-generated predicate function

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

   function Get_Flat_Statement_And_Declaration_List
     (Stmts : List_Id) return Node_Lists.List;
   --  Given a list of statements and declarations Stmts, returns the flattened
   --  list that includes these statements and declarations, and recursively
   --  all inner declarations and statements that appear in block statements.

   function Is_Others_Choice (Choices : List_Id) return Boolean;
   --  Returns True if Choices is the singleton list with an "others" element

   function Is_Standard_Entity (E : Entity_Id) return Boolean;
   --  This function is used to detect that an entity was defined in
   --  the standard library. They should correspond to node created by
   --  Create_Standard in cstand.ads.

   function File_Name_Without_Suffix (File_Name : String) return String;

   function Real_Image (U : Ureal; Max_Length : Integer) return String;
   --  Return a string, of maximum length Max_length, representing U.

   function String_Value (Str_Id : String_Id) return String;

   function Append_Multiple_Index (S : String) return String;
   --  If the current file contains multiple units, add a suffix to S that
   --  corresponds to the currently analyzed unit.

   function Unit_Name return String is
     (Append_Multiple_Index
        (File_Name_Without_Suffix
             (Get_Name_String (Unit_File_Name (Main_Unit)))));

   function File_Name (Loc : Source_Ptr) return String is
     (Get_Name_String (File_Name (Get_Source_File_Index (Loc))));
   --  @param Loc any source pointer
   --  @return the file name of the source pointer (will return the file of the
   --    generic in case of instances)

   function Contains_Volatile_Function_Call (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff the tree starting with N contains an N_Function_Call
   --    node whose callee is a function with pragma/aspect Volatile_Function
   --    set.

   function Contains_Allocator (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff the tree starting with N contains an N_Allocator
   --    node.

   function Safe_First_Sloc (N : Node_Id) return Source_Ptr
   with Post => (N = Empty) = (Safe_First_Sloc'Result = No_Location);
   --  Wrapper for First_Sloc that is safe to use for nodes coming from
   --  instances of generic units and subprograms inlined for proof.
   --  For valid nodes it returns a valid location; for an empty node it
   --  returns an invalid location.
   --
   --  ??? this is only a temporary fix and should be removed once the
   --  underlying problem with First_Sloc is fixed.

   function Entity_To_Subp_Assumption (E : Entity_Id) return Subp_Type
   with Pre => (if Is_Internal (E)
                then Is_Type (E) or else Is_Predicate_Function (E));
   --  Transform an entity into a Assumption_Types.Subp_Type
   --  ??? At the moment we are checking whether E is a predicate function but
   --  this will have to be removed as soon as we will not create graphs for
   --  type predicates.

   function Unique_Main_Unit_Entity return Entity_Id
   with Post => Ekind (Unique_Main_Unit_Entity'Result) in E_Function
                                                        | E_Procedure
                                                        | E_Package
                                                        | Generic_Unit_Kind;
   --  Wrapper for Lib.Main_Unit_Entity, which deals with library-level
   --  instances of generic subprograms (where the Main_Unit_Entity is
   --  has a void Ekind).

end SPARK_Util;
