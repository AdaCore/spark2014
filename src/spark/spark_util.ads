------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            S P A R K _ U T I L                           --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2012-2026, AdaCore                     --
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

with Ada.Containers.Hashed_Sets;
with Ada.Containers.Vectors;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Directories;
with Assumption_Types;      use Assumption_Types;
with Atree;                 use Atree;
with Checked_Types;         use Checked_Types;
with Common_Containers;     use Common_Containers;
with Einfo.Entities;        use Einfo.Entities;
with Einfo.Utils;           use Einfo.Utils;
with Lib;                   use Lib;
with Namet;                 use Namet;
with Nlists;                use Nlists;
with Sem_Aux;               use Sem_Aux;
with Sem_Util;              use Sem_Util;
with Sinfo.Nodes;           use Sinfo.Nodes;
with Sinput;                use Sinput;
with Snames;                use Snames;
with Types;                 use Types;
with Uintp;                 use Uintp;
with Urealp;                use Urealp;

package SPARK_Util is

   type True_Or_Explain (Ok : Boolean := True) is record
      case Ok is
         when True =>
            null;

         when False =>
            Explanation : Unbounded_String;
      end case;
   end record;
   --  Type to store a check result along with an explanation in case of
   --  failure.

   function False_With_Explain (S : String) return True_Or_Explain
   is (True_Or_Explain'(Ok => False, Explanation => To_Unbounded_String (S)));

   ---------------------------------------------------
   --  Utility types related to entities and nodes  --
   ---------------------------------------------------

   subtype N_Ignored_In_Marking is Node_Kind
   with
     Predicate =>
       N_Ignored_In_Marking
       in N_Call_Marker
        | N_Exception_Declaration
        | N_Freeze_Entity
        | N_Freeze_Generic_Entity
        | N_Implicit_Label_Declaration
        | N_Incomplete_Type_Declaration
        | N_Null_Statement
        | N_Number_Declaration
        | N_Representation_Clause

        --  Renamings are replaced by the renamed object in the frontend, but
        --  the renaming declarations are not removed from the tree. We can
        --  safely ignore them, except for renaming object declarations, which
        --  need to be analyzed for possible RTE.

        | N_Exception_Renaming_Declaration
        | N_Package_Renaming_Declaration
        | N_Subprogram_Renaming_Declaration
        | N_Generic_Renaming_Declaration

        --  Generic instantiations are expanded into the corresponding
        --  declarations in the frontend. The instantiations themselves can be
        --  ignored.

        | N_Package_Instantiation
        | N_Subprogram_Instantiation
        | N_Generic_Subprogram_Declaration
        | N_Generic_Package_Declaration
        | N_Use_Package_Clause
        | N_Use_Type_Clause
        | N_Validate_Unchecked_Conversion
        | N_Variable_Reference_Marker;

   --  After marking, ignore also labels (used in marking for targets of goto),
   --  and body stubs (used in marking to reach out to the proper bodies).
   subtype N_Ignored_In_SPARK is Node_Kind
   with
     Predicate =>
       N_Ignored_In_SPARK in N_Ignored_In_Marking | N_Label | N_Body_Stub;

   subtype N_Entity_Body is Node_Kind
   with Static_Predicate => N_Entity_Body in N_Proper_Body | N_Entry_Body;

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
      RCK_FP_Overflow_Not_First,
      RCK_Overflow_Not_Last,
      RCK_FP_Overflow_Not_Last);
   --  Kind for checks on scalar types

   type Continuation_Type is record
      Ada_Node : Node_Id;
      Message  : Unbounded_String;
   end record;
   --  Continuation message located at Ada_Node

   package Continuation_Vectors is new
     Ada.Containers.Vectors (Positive, Continuation_Type);

   type Bound_Info_Type is (No_Bound, Low_Bound, High_Bound);

   type Fix_Info_Type is record
      Range_Check_Ty : Opt_Type_Kind_Id;
      Divisor        : Node_Or_Entity_Id;
      Bound_Info     : Bound_Info_Type;
   end record;
   --  Extra information to get better possible fix messages

   type Check_Info_Type is record
      User_Message : String_Id;
      --  Message associated with an assertion/check pragma by the user
      Fix_Info     : Fix_Info_Type;
      Continuation : Continuation_Vectors.Vector;
      Subject      : Unbounded_String := Null_Unbounded_String;
      --  Additional information about the subject of the check
      Details      : Unbounded_String := Null_Unbounded_String;
      --  Additional details to be displayed when the check is not proved
   end record;
   --  Extra information for checks that is useful for generating better
   --  messages.

   type Inline_Info (Inline : Boolean := False) is record
      case Inline is
         when False =>
            null;

         when True =>
            Inline_Node : Node_Id;
      end case;
   end record;

   type Extra_Info is record
      Node       : Node_Id := Empty;
      Inline     : Inline_Info;
      Bound_Info : Bound_Info_Type := No_Bound;
   end record;
   --  Extra information to describe which part of a check is unproved

   subtype Volatile_Pragma_Id is Pragma_Id
   with
     Static_Predicate =>
       Volatile_Pragma_Id
       in Pragma_Async_Readers
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

   procedure Set_Specific_Tagged (E : Class_Wide_Kind_Id; V : Record_Kind_Id);
   --  Create a link from the classwide type to its specific tagged type
   --  in SPARK, which can be either V or its partial view if the full view of
   --  V is not in SPARK.
   --  @param E classwide type
   --  @param V specific tagged type corresponding to the classwide type E

   function Specific_Tagged (E : Class_Wide_Kind_Id) return Record_Kind_Id;
   --  @param E classwide type
   --  @return the specific tagged type corresponding to classwide type E

   procedure Set_Visible_Overridden_Operation (E, Inh : Callable_Kind_Id)
   with
     Pre =>
       E = Ultimate_Alias (E)
       and Inh = Ultimate_Alias (Inh)
       and Is_Dispatching_Operation (E)
       and Is_Dispatching_Operation (Inh);
   --  Register than E is overriding Inh according to SPARK visibility of
   --  inheritance.

   function Visible_Overridden_Operation
     (E : Callable_Kind_Id) return Entity_Id
   with
     Pre  => E = Ultimate_Alias (E),
     Post =>
       (declare
          R : constant Entity_Id := Visible_Overridden_Operation'Result;
        begin
          (if not Is_Dispatching_Operation (E)
           then No (R)
           elsif Present (R)
           then R = Ultimate_Alias (R) and Is_Dispatching_Operation (R)));
   --  Return the SPARK operation overridden by E, according to SPARK
   --  visibility of inheritance, or Empty if there are none.
   --  Using SPARK visibility of inheritance means that any intermediate
   --  overriding procedures in a private part with SPARK_Mode Off are not
   --  taken into account, effectively skipped. However, procedures with
   --  SPARK_Mode Off whose type is a visible ancestor are not skipped, and
   --  may 'cut' an overriding.

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
     (Ref : Entity_Id; Context : Entity_Id) return Entity_Id
   with
     Pre =>
       Ekind (Context)
       in Entry_Kind
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

   function Dispatching_Contract (L : Node_Lists.List) return Node_Lists.List;
   --  Same as above but with a list of classwide pre- or postconditions

   procedure Set_Call_Simulates_Contract_Dispatch (N : Node_Id)
   with
     Pre =>
       Nkind (N) in N_Function_Call | N_Op_Eq | N_Membership_Test
       and then
         (if Nkind (N) = N_Function_Call
          then Present (Controlling_Argument (N)));
   --  Register that a dispatching call is one produced by GNATprove to model
   --  contract dispatch.
   --
   --  When a dispatching call is performed, the subprogram and the contract
   --  are resolved as a whole. GNATprove creates a contract containing
   --  dispatching calls to simulate selection of the contract, breaking down
   --  that wholesale selection in pieces. However, these calls do not mirror
   --  real dispatching calls. In particular, there is no associated runtime
   --  tag check. The equality operator (and membership tests that
   --  implicitly use it) may also appear due to primitive equality, which
   --  should be modeled by calls to dispatching equality. Due to the
   --  differences in handling, we need a way to distinguish these cases.

   function Call_Simulates_Contract_Dispatch (N : Node_Id) return Boolean;
   --  Return True if N is a function call that has been introduced to simulate
   --  contract dispatch.

   procedure Set_Conditional_Old_Attribute
     (Prefix : Node_Id; Condition : Node_Id);
   --  Register Prefix of an 'Old attribute reference as conditionally
   --  evaluated, with the condition under which it should be evaluated.

   function Condition_Of_Conditional_Old (Prefix : Node_Id) return Node_Id;
   --  For a prefix of an 'Old attribute which is conditionally evaluated,
   --  return the condition under which it is evaluated. For other nodes,
   --  return Empty.

   -----------------------------------------
   -- General queries related to entities --
   -----------------------------------------

   function Alternative_Uses_Eq (Alt : Node_Id) return Boolean;
   --  Return True if the evaluation of a membership test with Alt
   --  involves an equality relation.

   function Enclosing_Generic_Instance (E : Entity_Id) return Opt_E_Package_Id;
   --  @param E any entity
   --  @return entity of the enclosing generic instance package, if any

   function Enclosing_Unit (E : Entity_Id) return Unit_Kind_Id;
   --  Returns the entity of the package, subprogram, entry, protected type,
   --  task type, or subprogram type enclosing E.

   function Directly_Enclosing_Subprogram_Or_Entry
     (E : Entity_Id) return Opt_Callable_Kind_Id;
   --  Returns the entity of the first subprogram or entry enclosing E. Returns
   --  Empty if there is no such subprogram or if something else than a package
   --  (a concurrent type or a block statement) is encountered while going up
   --  the scope of E

   function Entity_Comes_From_Source (E : Entity_Id) return Boolean
   is (Comes_From_Source (E) or else Comes_From_Source (Atree.Parent (E)));
   --  Ideally we should only look at whether entity E comes from source,
   --  but in various cases this is not properly set in the frontend (for
   --  subprogram inlining and generic instantiations), which cannot be fixed
   --  easily. So we also look at whether the parent node comes from source,
   --  which is more often correct.

   function Full_Name (E : Entity_Id) return String;
   --  @param E any entity
   --  @return the name to use for E in Why3

   function Full_Name_Is_Not_Unique_Name (E : Entity_Id) return Boolean;
   --  In almost all cases, the name to use for an entity in Why3 is based on
   --  its unique name in GNAT AST, so that this name can be used everywhere
   --  to refer to the entity (for example to retrieve completion theories).
   --  A few cases require special handling because their name is predefined
   --  in Why3. This concerns currently only Standard_Boolean and its full
   --  subtypes.
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

   function Is_Declared_Directly_In_Unit
     (E : Entity_Id; Scope : Entity_Id) return Boolean;
   --  @param E any entity
   --  @param Scope scope
   --  @return True iff E is declared directly in Scope

   function Is_Declared_In_Unit
     (E : Entity_Id; Scope : Entity_Id) return Boolean;
   --  @param E any entity
   --  @param Scope scope
   --  @return True iff E is declared in Scope or in one of its (recursively)
   --    nested packages.

   function Is_Declared_In_Main_Unit_Or_Parent (N : Node_Id) return Boolean;
   --  @param N any node which is not in Standard
   --  @return True iff N is declared in the analysed unit or any of its
   --     parents.

   function Is_Declared_In_Private (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E is declared in the private part of a package

   function Is_Declared_In_Statements (Decl : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is directly in a sequence of statements

   function Is_Private_Child_Unit (E : Entity_Id) return Boolean
   with Pre => Is_Child_Unit (E);
   --  Return True if E is a private child unit

   function Is_In_Potentially_Hidden_Private (E : Entity_Id) return Boolean;
   --  Return True if E is defined in the private part of a package annotated
   --  with a Hide_Info "Private_Part" annotation.

   function Hide_For_Current_Analysis (N : Node_Id) return Boolean;
   --  Return True if potentially hidden entities declared in node N should be
   --  considered hidden during the current analysis.

   function Is_In_Hidden_Private (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E is hidden by a Hide_Info "Private_Part" annotation
   --     for the current analysis.

   function Is_Ignored_Internal (N : Node_Or_Entity_Id) return Boolean
   is (In_Internal_Unit (N) and then not Is_Internal_Unit (Main_Unit));
   --  @return True iff N can be ignored because it is an internal node and the
   --  current unit analyzed is not internal.

   function In_SPARK_Library_Unit (N : Node_Or_Entity_Id) return Boolean;
   --  Return True if the source unit for N is in the SPARK library, ie. if
   --  the unit name starts with "spark-" and ends with ".ads" or ".adb".

   function Is_In_Analyzed_Files (E : Entity_Id) return Boolean;
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

   function Raw_Source_Name (N : Node_Id) return String
   with Pre => Present (N) and then Nkind (N) in N_Has_Chars;
   --  @param N any node with Chars field
   --  @return The unqualified name of N as it appears in the source code

   function Pretty_Source_Name (N : Node_Id) return String
   with Pre => Present (N) and then Nkind (N) in N_Has_Chars;
   --  @param N any node with Chars field
   --  @return Same as above but use pretty printing and try to avoid internal
   --     names. It should only be used in messages.

   function Is_Local_Context (Scop : Entity_Id) return Boolean;
   --  Return if a given scope defines a local context where it is legal to
   --  declare a variable of anonymous access type.

   ----------------------------------------------
   -- Queries related to objects or components --
   ----------------------------------------------

   function Comes_From_Declare_Expr (E : Entity_Id) return Boolean;
   --  True if E is an object declared in an expression with actions. In SPARK,
   --  this should correspond to a declare expression.

   function Component_Is_Visible_In_SPARK (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Component | E_Discriminant;
   --  @param E component
   --  @return True iff the component E should be visible in the translation
   --     into Why3, i.e. it is a discriminant (which cannot be hidden in
   --     SPARK) or the full view of the enclosing record is in SPARK.

   function Enclosing_Concurrent_Type (E : Entity_Id) return Concurrent_Kind_Id
   with
     Pre =>
       Is_Part_Of_Concurrent_Object (E)
       or else Is_Concurrent_Component_Or_Discr (E);
   --  @param E is the entity of a component, discriminant or Part of
   --     concurrent type
   --  @return concurrent type

   function Has_Volatile (E : N_Entity_Id) return Boolean
   with
     Pre  =>
       Ekind (E)
       in E_Abstract_State
        | E_Protected_Type
        | E_Task_Type
        | Object_Kind
        | Type_Kind,
     Post =>
       (if Ekind (E) in E_Protected_Type | E_Task_Type
        then not Has_Volatile'Result);
   --  @param E an abstract state, object (including concurrent types, which
   --     might be implicit parameters and globals) or type
   --  @return True iff E is an external state or a volatile object or type

   function Has_Volatile_Property
     (E : N_Entity_Id; P : Volatile_Pragma_Id) return Boolean
   with Pre => Has_Volatile (E);
   --  @param E an external state, a volatile object or type, or a protected
   --     component
   --  @return True iff E has the specified property P of volatility, either
   --     directly or through its (base) type.

   function Is_Constant_After_Elaboration (E : E_Variable_Id) return Boolean;
   --  @param E entity of a variable
   --  @return True iff a Constant_After_Elaboration applies to E

   function Is_Constant_In_SPARK (E : Object_Kind_Id) return Boolean;
   --  Return True if E is a constant in SPARK (ie. a constant which is not
   --  of access-to-variable type).

   function Is_Concurrent_Component_Or_Discr (E : Entity_Id) return Boolean;
   --  @param E an entity
   --  @return True iff the entity is a component or discriminant of a
   --            concurrent type

   function Is_Constant_Borrower (E : Object_Kind_Id) return Boolean
   with Pre => Is_Local_Borrower (E);
   --  Return True if E is a local borrower which is acting like an observer
   --  (it is directly or indirectly rooted at the first parameter of a
   --  borrowing traversal function).

   function Is_Deep_Delta_Aggregate (Exp : Node_Id) return Boolean;
   --  Return True on deep delta aggregates

   function Is_For_Loop_Parameter (E : Entity_Id) return Boolean;
   --  Returns True iff E is the loop parameter of a for loop with a loop
   --  parameter specification.

   function Is_Global_Entity (E : Entity_Id) return Boolean;
   --  Returns True iff E represent an entity that can be a global

   function Is_Local_Borrower (E : Entity_Id) return Boolean;
   --  Return True if E is a constant or a variable of an anonymous access to
   --  variable type.

   function Is_Not_Hidden_Discriminant (E : E_Discriminant_Id) return Boolean;
   --  @param E entity of a discriminant
   --  @return Return True if E is visible in SPARK. A discriminant might not
   --    be visible if it cames from the full view of a private type which
   --    is not in SPARK.

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
   is (Is_Protected_Component_Or_Discr (E)
       or else Is_Part_Of_Protected_Object (E));
   --  @param E an entity
   --  @return True iff E is logically part of a protected object, either being
   --    a discriminant of field of the object, or being a "part_of".

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Loop_Parameter | E_Variable;
   --  @param E loop parameter
   --  @return True iff E has been introduced by a quantified expression

   function Is_Quantified_Param_Over_Array (Obj : Entity_Id) return Boolean;
   --  Return True iff E has been introduced by a quantified expression over
   --  the elements of an array.

   function Is_Synchronized (E : Entity_Id) return Boolean
   with
     Pre =>
       Ekind (E)
       in E_Abstract_State | E_Protected_Type | E_Task_Type | Object_Kind;
   --  @param E an entity that represents a global
   --  @return True if E is safe to be accesses from multiple tasks

   function Is_Writable_Parameter (E : Entity_Id) return Boolean
   with
     Pre =>
       Ekind (E) = E_In_Parameter
       and then
         Ekind (Scope (E))
         in E_Procedure | E_Function | E_Entry | E_Subprogram_Type
       and then
         (if Ekind (Scope (E)) = E_Function
          then Is_Function_With_Side_Effects (Scope (E)));
   --  @param E entity of a procedure or entry formal parameter of mode IN
   --  @return True if E can be written despite being of mode IN

   function Root_Discriminant (E : E_Discriminant_Id) return Entity_Id;
   --  Given discriminant of a record (sub-)type, return the corresponding
   --  discriminant of the root retysp, if any. This is the identity when E is
   --  the discriminant of a root type.

   function Search_Component_By_Name
     (Rec : Record_Like_Kind_Id; Comp : Record_Field_Kind_Id)
      return Opt_Record_Field_Kind_Id;
   --  Given a record type entity and a component/discriminant entity, search
   --  in Rec a component/discriminant entity with the same name and the same
   --  original record component. Returns Empty if no such component is found.
   --  In particular returns empty on hidden components.

   function Unique_Component
     (E : Record_Field_Kind_Id) return Record_Field_Kind_Id
   with Post => Ekind (Unique_Component'Result) = Ekind (E);
   --  Given an entity of a record component or discriminant, possibly from a
   --  derived type, return the corresponding component or discriminant from
   --  the base type. The returned entity provides a unique representation of
   --  components and discriminants between both the base type and all types
   --  derived from it.

   function Is_Unique_Component (E : Entity_Id) return Boolean
   is (E = Unique_Component (E))
   with Ghost;
   --  A trivial wrapper to be used in assertions when converting from the
   --  frontend to flow representation of discriminants and components.

   procedure Compatible_Alignments
     (X           : Constant_Or_Variable_Kind_Id;
      YY          : Node_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   with Post => Result = (Explanation = Null_Unbounded_String);
   --  @param X a stand-alone object that overlays the other
   --            (object with Address clause)
   --  @param YY object that is overlaid (object whose 'Address is used in
   --            the Address clause of X)
   --  @return True iff X'Alignment and Y'Alignment are known and Y'Alignment
   --          is an integral multiple of X'Alignment

   --------------------------------
   -- Queries related to pragmas --
   --------------------------------

   function Is_Ignored_Pragma_Check (N : N_Pragma_Id) return Boolean;
   --  @param N pragma
   --  @return True iff N is a pragma Check that can be ignored by analysis,
   --     because it is already taken into account elsewhere (precondition,
   --     postcondition, predicates).

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

   function Is_Pragma_Assert_And_Cut (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is a pragma Assert_And_Cut

   ---------------------------------
   -- Queries for arbitrary nodes --
   ---------------------------------

   function String_Of_Node (N : N_Subexpr_Id) return String;
   --  @param N any expression node
   --  @return the node as pretty printed Ada code, limited to 50 chars

   generic
      with function Property (N : Node_Id) return Boolean;
   function First_Parent_With_Property (N : Node_Id) return Node_Id
   with
     Post =>
       No (First_Parent_With_Property'Result)
       or else Property (First_Parent_With_Property'Result);
   --  @param N any node
   --  @return the first node in the chain of parents of N for which Property
   --     returns True.

   function Get_Initialized_Object
     (N : N_Subexpr_Id) return Opt_Object_Kind_Id;
   --  @param N any expression node
   --  @return if N is used to initialize an object, return this object. Return
   --      Empty otherwise. This is used to get a stable name for aggregates
   --      used as definition of objects.

   function In_Loop_Entry_Or_Old_Attribute (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True if the node is a Loop_Entry or Old attribute

   function Is_In_Statically_Dead_Branch (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True if the node is in a branch that is statically dead. Only
   --      if-statements are detected for now.

   function Is_Within_Finally_Section (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True if the node is in a finally section.

   function May_Issue_Warning_On_Node (N : Node_Id) return Boolean;
   --  We do not issue any warnings on nodes which stem from inlining or
   --  instantiation, or in subprograms or library packages whose analysis
   --  has not been requested, such as subprograms that are always inlined
   --  in proof.

   function Shape_Of_Node (Node : Node_Id) return String;
   --  Return a string representing the shape of the Ada code surrounding the
   --  input node. This is used to name the VC file for manual proof.

   type Location_String_Mode is
     (Check_Label_Mode,          --  location for a VC
      Limit_Subp_Mode,           --  location in --limit-subp switch
      Data_Decomposition_Mode);  --  location in JSON files for data info

   function Location_String
     (Input : Source_Ptr; Mode : Location_String_Mode) return String;
   --  Build a string that represents the source location of the source
   --  pointer, taking into account the intended use of this string, so that
   --  it includes or not the chain of generic instantiations, and the columns.
   --  The order in the chain of instantiations also depends on the intended
   --  use.

   ----------------------------------
   -- Queries for particular nodes --
   ----------------------------------

   function Aggregate_Is_In_Assignment (Expr : Node_Id) return Boolean
   with Pre => Expr in N_Aggregate_Kind_Id or else Is_Attribute_Update (Expr);
   --  Returns whether Expr is on the rhs of an assignment, either directly or
   --  through other enclosing aggregates, with possible type conversions and
   --  qualifications.

   type Unrolling_Type is
     (No_Unrolling,
      Simple_Unrolling,
      --  body of the loop repeated N times
      Unrolling_With_Condition
      --  value used for unrolling with a condition to check loop test, which
      --  is necessary when the loop has a dynamic range
     );

   function Is_Selected_For_Loop_Unrolling
     (Loop_Stmt : N_Loop_Statement_Id) return Boolean;
   --  Return whether [Loop_Stmt] is unrolled or not

   procedure Candidate_For_Loop_Unrolling
     (Loop_Stmt   : N_Loop_Statement_Id;
      Output_Info : Boolean;
      Result      : out Unrolling_Type;
      Low_Val     : out Uint;
      High_Val    : out Uint);
   --  @param Output_Info whether the reason for not unrolling should be
   --         displayed when the loop has no loop invariant, and a positive
   --         message that the loop is unrolled when applicable.
   --  @param Result whether a loop is a candidate for loop unrolling
   --  @param Low_Val the loop bound for loop unrolling
   --  @param High_Val the high bound for loop unrolling

   function Enclosing_Statement_Of_Call_To_Function_With_Side_Effects
     (Call : Node_Id) return Node_Id;
   --  Return the statement enclosing Call which is a call to a function with
   --  side-effects.

   function Full_Protected_Name (N : Node_Id) return String
   with
     Pre =>
       Nkind (N)
       in N_Expanded_Name
        | N_Identifier
        | N_Indexed_Component
        | N_Slice
        | N_Selected_Component;
   --  @param N is a prefix of an entry call; it denotes either a stand-alone
   --     protected object or a component of a protected type within a
   --     composite object
   --  @return a name that uniquely identifies the prefix

   function Generic_Actual_Subprograms (E : E_Package_Id) return Node_Sets.Set
   with
     Pre  => Is_Generic_Instance (E),
     Post =>
       (for all S of Generic_Actual_Subprograms'Result => Is_Subprogram (S));
   --  @param E instance of a generic package (or a wrapper package for
   --    instances of generic subprograms)
   --  @return actual subprogram parameters of E

   function Parent_Instance_From_Child_Unit (E : Entity_Id) return Entity_Id
   with Pre => Is_Generic_Instance (E);
   --  Get the instance of the parent from the instance of a child package

   function Get_Formal_From_Actual
     (Actual : N_Subexpr_Id) return Formal_Kind_Id
   with
     Pre =>
       Nkind (Parent (Actual))
       in N_Subprogram_Call
        | N_Entry_Call_Statement
        | N_Parameter_Association
        | N_Unchecked_Type_Conversion;
   --  @param Actual actual parameter of a call (or expression of an unchecked
   --    conversion which comes from a rewritten call to instance of
   --    Ada.Unchecked_Conversion)
   --  @return the corresponding formal parameter

   function Get_Operator_Symbol (N : Node_Id) return String
   with Pre => Is_Operator_Symbol_Name (Chars (N));
   --  Lookup function (based on the contents of the Snames package) to
   --  convert "operator symbol" to a user-meaningful operator.

   function Get_Range (N : Node_Id) return Node_Id
   with
     Post =>
       Present (Low_Bound (Get_Range'Result))
       and then Present (High_Bound (Get_Range'Result));
   --  @param N more or less any node which has some kind of range, e.g. a
   --     scalar type entity or occurrence, a variable of such type, the type
   --     declaration or a subtype indication.
   --  @return the N_Range node of such a node

   function Get_Observed_Or_Borrowed_Expr
     (Expr : N_Subexpr_Id) return N_Subexpr_Id
   with Pre => Is_Path_Expression (Expr);
   --  Return the expression being borrowed/observed when borrowing or
   --  observing Expr, as computed by Get_Observed_Or_Borrowed_Info.

   procedure Get_Observed_Or_Borrowed_Info
     (Expr   : N_Subexpr_Id;
      B_Expr : out N_Subexpr_Id;
      B_Ty   : in out Opt_Type_Kind_Id)
   with Pre => Is_Path_Expression (Expr);
   --  Compute both the expression being borrowed/observed when borrowing or
   --  observing Expr and the type used for this borrow/observe.
   --  @param Expr a path used for a borrow/observe
   --  @param B_Expr the expression being borrowed/observed when borrowing or
   --      observing Expr. If Expr contains a call to traversal function, this
   --      is the first actual of the first such call, otherwise it is Expr.
   --  @param B_Ty the type of the first borrower/observer in Expr. If Expr
   --      contains a call to traversal function, this is the type of the first
   --      formal of the function, otherwise it is B_Ty.
   --      Note that B_Ty is not the type of B_Expr but a compatible anonymous
   --      access type.

   function Get_Root_Expr
     (Expr : N_Subexpr_Id; Through_Traversal : Boolean := True)
      return N_Subexpr_Id
   with Pre => Is_Path_Expression (Expr);
   --  Return the root of the path expression Expr (object, aggregate,
   --  allocator, NULL, or function call). Through_Traversal is True if it
   --  should follow through calls to traversal functions.
   --  For actual conditional path selections, this return the root of the
   --  first branch. It should only be used when all branches have equivalent
   --  roots.

   function Get_Root_Object
     (Expr : N_Subexpr_Id; Through_Traversal : Boolean := True)
      return Opt_Object_Kind_Id
   with Pre => Is_Conditional_Path_Selection (Expr);
   --  Return the root of the path expression Expr, or Empty for an allocator,
   --  NULL, or a function call. Through_Traversal is True if it should follow
   --  through calls to traversal functions.
   --  For actual conditional path selections, this return a root only if all
   --  branches have the same root object, otherwise it returns empty.

   function Get_Specialized_Parameters
     (Call                 : Node_Id;
      Specialized_Entities : Node_Maps.Map := Node_Maps.Empty_Map)
      return Node_Maps.Map;
   --  @param Call any node
   --  @param Specialized_Entities map of formal parameter which are
   --     specialized in the current context.
   --  @return a map which associates specialized formals in a function call
   --  with higher order specialization to the actual entity.

   function Is_Access_Attribute_Of_Function (Expr : Node_Id) return Boolean;
   --  Return True if Expr is an access attribute on a function identifier

   function Is_Action (N : N_Object_Declaration_Id) return Boolean;
   --  @param N is an object declaration
   --  @return if the given node N is an action

   function Is_Converted_Actual_Output_Parameter
     (N : N_Subexpr_Id) return Boolean;
   --  @param N expression
   --  @return True iff N is either directly an out or in out actual parameter,
   --     or under one or multiple type conversions, where the most enclosing
   --     type conversion is an out or in out actual parameter.

   function Is_Call_Arg_To_Predicate_Function
     (N : Opt_N_Subexpr_Id) return Boolean;
   --  @param N expression node or Empty
   --  @return True iff N is the argument to a call to a frontend-generated
   --     predicate function. This should only occur when analyzing the code
   --     for the predicate function of a derived type, so the argument
   --     should take the form of a type conversion. Node N should be the
   --     expression being converted rather than the type conversion itself.

   function Is_Empty_Others
     (N : N_Case_Statement_Alternative_Id) return Boolean
   with
     Post =>
       (if Is_Empty_Others'Result
        then No (Next (N)) and then List_Length (Discrete_Choices (N)) = 1);
   --  Returns True iff N is an "others" case alternative with empty set
   --  of discrite choices (this set is statically determined by the front
   --  end). Such an alternative must not be followed by other alternatives
   --  and "others" must be its only choice.

   function Is_Error_Signaling_Statement (N : Node_Id) return Boolean;
   --  Returns True iff N is a statement used to signal an error:
   --    . a raise statement or expression
   --    . a pragma Assert (False)
   --    . a call to an error-signaling procedure
   --    . a call to a function with precondition False

   function Is_External_Call (N : N_Call_Id) return Boolean
   with Pre => Within_Protected_Type (Get_Called_Entity (N));
   --  @param N call node
   --  @return True iff N is an external call to a protected subprogram or
   --     a protected entry.
   --
   --  Note: calls to protected functions in preconditions and guards of the
   --  Contract_Cases are external, but this routine treats them as internal.
   --  However, the front end rejects these two cases. For the SPARK back end,
   --  this routine gives correct results.

   function Is_In_Toplevel_Move (N : N_Subexpr_Id) return Boolean;
   --  Return True if N occurs directly at a place where moves are alloxed, ie
   --  as the expression of an object declaration occuring outside of a
   --  declare block, as the lefthand side of an assignment, or in a simple
   --  return statement.

   function Is_Path_Expression (Expr : N_Subexpr_Id) return Boolean;
   --  Return whether Expr corresponds to a path

   function Is_Conditional_Path_Selection (Expr : N_Subexpr_Id) return Boolean;
   --  Return whether Expr is a conditional path selection, that is a nest of
   --  conditional/case expressions (possibly empty) whose terminal dependent
   --  expressions are paths.

   function Is_Strict_Subpath (Expr : N_Subexpr_Id) return Boolean
   with
     Pre =>
       Is_Path_Expression (Expr) and then Present (Get_Root_Object (Expr));
   --  Return True is the structure referenced from Expr is a strictly
   --  smaller substructure of the structure referenced from its root.

   function Is_Predicate_Function_Call (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is a call to a frontend-generated predicate function

   function Is_Singleton_Choice (Choices : List_Id) return Boolean;
   --  Return whether Choices is a singleton choice

   function Is_Specializable_Formal (Formal : Formal_Kind_Id) return Boolean;
   --  Return True if Formal can be specialized, ie. it is an IN parameter of
   --  an anonymous access-to-function type.

   function Is_Specialized_Actual
     (Expr                 : Node_Id;
      Specialized_Entities : Node_Maps.Map := Node_Maps.Empty_Map)
      return Boolean;
   --  @param Expr any node
   --  @param Specialized_Entities map of formal parameter which are
   --     specialized in the current context.
   --  @return True iff Expr is a parameter of a call to a function annotated
   --     with higher order specialization and it needs special handling.

   function Is_Specialized_Call
     (Call                 : Node_Id;
      Specialized_Entities : Node_Maps.Map := Node_Maps.Empty_Map)
      return Boolean;
   --  @param Call any node
   --  @param Specialized_Entities map of formal parameter which are
   --     specialized in the current context.
   --  @return True if Call is a call to a function with higher order
   --  specialization which has at least a specialized parameter.
   --  ??? We could also consider the call to be specialized only if at
   --  least one of its specialized parameters has global inputs.

   function Is_Null_Or_Reclaimed_Expr
     (Expr       : N_Subexpr_Id;
      Reclaimed  : Boolean := False;
      Null_Value : Boolean := False) return Boolean;
   --  If Expr has an access type, it returns True iff Expr is statically null.
   --  If Expr is a private type and Reclaimed is True, return True if Expr is
   --  statically known to be a constant with the Reclaimed_Value annotation.
   --  If Expr is a private type and Null_Value is True, return
   --  True if Expr is statically known to be a constant with the
   --  Null_Value annotation.

   function Is_Null_Or_Reclaimed_Obj
     (Obj        : Object_Kind_Id;
      Reclaimed  : Boolean := False;
      Null_Value : Boolean := False) return Boolean;
   --  Same as above but with an object. Look through the definition of
   --  constants.

   function Is_Non_Exec_Assertion_Level (Level : Entity_Id) return Boolean;
   --  Return true on an assertion level that cannot be enabled at runtime

   function In_Non_Exec_Context (N : Node_Id) return Boolean;
   --  Return True if N is in a ghost context that cannot be enabled at
   --  runtime. This function does not check whether the enclosing unit itself
   --  is non-executable.

   function In_Statically_Leaking_Context
     (Expr : N_Subexpr_Id; Ignore_Non_Exec : Boolean) return Boolean;
   --  Return True if Expr occurs in a context where it is statically known
   --  to not be possible to reclaim. This happens for expressions that are
   --  part of an assertion pragma. If Ignore_Non_Exec is True, only consider
   --  pragmas that can be enabled at runtime.

   function Is_Traversal_Function_Call (Expr : Node_Id) return Boolean;
   --  @param Expr any node
   --  @return True iff Expr is a call to a traversal function

   function Loop_Entity_Of_Loop_Jump_Statement (N : Node_Id) return Entity_Id
   with Pre => Nkind (N) in N_Exit_Statement | N_Continue_Statement;
   --  Return the Defining_Identifier of the loop that belongs to a
   --  transfer-of-control statement associated to loops.

   function Loop_Entity_Of_Continue_Statement
     (N : N_Continue_Statement_Id) return Entity_Id
   renames Loop_Entity_Of_Loop_Jump_Statement;
   --  Return the Defining_Identifier of the loop that belongs to a continue
   --  statement.

   function Loop_Entity_Of_Exit_Statement
     (N : N_Exit_Statement_Id) return Entity_Id
   renames Loop_Entity_Of_Loop_Jump_Statement;
   --  Return the Defining_Identifier of the loop that belongs to an exit
   --  statement.

   function Number_Of_Assocs_In_Expression (N : Node_Id) return Natural;
   --  @param N any node
   --  @return the number of N_Component_Association nodes in N.

   function Expr_Has_Relaxed_Init
     (Expr : N_Subexpr_Id; No_Eval : Boolean := True) return Boolean;
   --  Return True if Expr is an expression with relaxed initialization. If
   --  No_Eval is True, then we don't consider the expression to be evaluated.

   function Obj_Has_Relaxed_Init (Obj : Object_Kind_Id) return Boolean;
   --  Return True if Obj is an object with relaxed initialization

   function Fun_Has_Relaxed_Init (Subp : E_Function_Id) return Boolean;
   --  Return True if the result of Subp has relaxed initialization

   function Expr_Has_Relaxed_Discr (Expr : N_Subexpr_Id) return Boolean;
   --  Return True if Expr is an expression with relaxed initialization whose
   --  discriminants might not be initialized.
   --  As this fonction is only used to reject 'Initialized on discriminants
   --  in marking, it only expects objects as inputs.

   function Borrower_For_At_End_Borrow_Call
     (Call : N_Function_Call_Id) return Entity_Id;
   --  From a call to a function annotated with At_End_Borrow, get the entity
   --  whose scope the at end refers to.

   procedure Set_At_End_Borrow_Call
     (Call : N_Function_Call_Id; Borrower : Entity_Id);
   --  Store the link between a call to a function annotated with
   --  At_End_Borrow and the entity whose scope the at end refers to.

   function Is_Prophecy_Save (E : Entity_Id) return Boolean;
   --  Checks whether E is used to save a prophecy variable.

   procedure Register_Prophecy_Save (E : Entity_Id);
   --  Registers that E saves a prophecy variable.

   function Path_Contains_Witness
     (Expr : N_Subexpr_Id;
      Test : not null access function (N : Node_Id) return Boolean)
      return Boolean
   with Pre => Is_Path_Expression (Expr);
   --  Check whether the path contains a node satisfying predicate Test.

   function Path_Contains_Qualified_Expr (Expr : N_Subexpr_Id) return Boolean
   with
     Pre =>
       Is_Path_Expression (Expr) and then Present (Get_Root_Object (Expr));
   --  Return True if the path from Expr contains a qualified expression

   function Path_Contains_Traversal_Calls
     (Expr : N_Subexpr_Id; Only_Observe : Boolean := False) return Boolean
   with Pre => Is_Path_Expression (Expr);
   --  Return True if the path from Expr contains a call to a traversal
   --  function. If Only_Observe is True, borrowing traversal functions are
   --  ignored.

   function Traverse_Access_To_Constant (Expr : N_Subexpr_Id) return Boolean
   with Pre => Is_Path_Expression (Expr);
   --  Return True if the path from Expr goes through a dereference of an
   --  access-to-constant type.

   function Is_Rooted_In_Constant (Expr : N_Subexpr_Id) return Boolean;
   --  Return True if Expr is a path rooted inside a constant part of an
   --  object. We do not return True if Expr is rooted inside an IN parameter,
   --  as the actual might be a variable object.

   function Terminal_Alternatives
     (Expr : N_Subexpr_Id) return Node_Vectors.Vector;
   --  From a nest of conditional/case expressions (possibly empty), return the
   --  sequence of terminal dependent subexpressions of Expr.

   ---------------------------------
   -- Misc operations and queries --
   ---------------------------------

   function To_String (N : Name_Id; Sloc : Source_Ptr) return String;
   --  Similar to Errout.Set_Msg_Insertion_Name, but directly returns a string
   --  instead of operating on a global buffer.

   procedure Append (To : in out Node_Lists.List; Elmts : Node_Lists.List);
   --  Append all elements from list Elmts to the list To

   function Char_To_String_Representation (C : Character) return String;
   --  @param C a character to print in a counterexample
   --  @return a string representing the character for humans to read, which is
   --     the character itself if it is a graphic one, otherwise its name.

   function Is_Null_Owning_Access (Expr : Node_Id) return Boolean
   is (Nkind (Expr) = N_Null
       and then
         (Is_Anonymous_Access_Type (Etype (Expr))
          or else Is_Access_Variable (Etype (Expr))));
   --  Return True if Expr is exactly null and has an anomyous access type
   --  or an access-to-variable type.
   --  This is used to recognize actuals of calls which are not a part of a
   --  variable object though they are used as a mutable parameter.

   function Is_Others_Choice (Choices : List_Id) return Boolean;
   --  Returns True if Choices is the singleton list with an "others" element

   function Real_Image (U : Ureal; Max_Length : Integer) return String;
   --  Return a string, of maximum length Max_length, representing U.

   function String_Value (Str_Id : String_Id) return String
   with Pre => Str_Id /= No_String;

   function Append_Multiple_Index (S : String) return String;
   --  If the current file contains multiple units, add a suffix to S that
   --  corresponds to the currently analyzed unit.

   function Unit_Name return String
   is (Append_Multiple_Index
         (Ada.Directories.Base_Name
            (Get_Name_String (Unit_File_Name (Main_Unit)))));

   function File_Name (Loc : Source_Ptr) return String
   is (Get_Name_String (File_Name (Get_Source_File_Index (Loc))));
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

   function Contains_Cut_Operations (N : N_Subexpr_Id) return Boolean;
   --  @param N an expression
   --  @return True iff the tree starting with N contains a call to a cut
   --    operation. Takes advantage of the supported context for these nodes
   --    to cut branches.

   function Contains_Function_Call (N : Node_Id) return Boolean;
   --  Return True iff N contains an N_Function_Call node

   function Is_Function_Call_With_Side_Effects (N : Node_Id) return Boolean;
   --  @param N any node
   --  @return True iff N is an N_Function_Call node whose callee is a function
   --    annotated with Side_Effects.

   function Safe_First_Sloc (N : Node_Id) return Source_Ptr
   with Post => (N = Empty) = (Safe_First_Sloc'Result = No_Location);
   --  Wrapper for First_Sloc that is safe to use for nodes coming from
   --  instances of generic units and subprograms inlined for proof.
   --  For valid nodes it returns a valid location; for an empty node it
   --  returns an invalid location.
   --
   --  ??? this is only a temporary fix and should be removed once the
   --  underlying problem with First_Sloc is fixed.

   function Safe_Last_Sloc (N : Node_Id) return Source_Ptr;
   --  Wrapper for Last_Sloc, similar to Safe_First_Sloc.

   function Entity_To_Subp_Assumption (E : Entity_Id) return Subp_Type
   with
     Pre =>
       (if Is_Internal (E) then Is_Type (E) or else Is_Predicate_Function (E));
   --  Transform an entity into a Assumption_Types.Subp_Type
   --  ??? At the moment we are checking whether E is a predicate function but
   --  this will have to be removed as soon as we will not create graphs for
   --  type predicates.

   function Unique_Main_Unit_Entity return Entity_Id
   with
     Post =>
       Ekind (Unique_Main_Unit_Entity'Result)
       in E_Function | E_Procedure | E_Package | Generic_Unit_Kind;
   --  Wrapper for Lib.Main_Unit_Entity, which deals with library-level
   --  instances of generic subprograms (where the Main_Unit_Entity has a
   --  void Ekind).

   function Attr_Constrained_Statically_Known (N : Node_Id) return Boolean;
   --  Approximation of cases where we know that the Constrained attribute of
   --  N is known statically.

   function Statement_Enclosing_Label (E : E_Label_Id) return Node_Id;
   --  Return the parent of the N_Label node associated to E

   function States_And_Objects (E : E_Package_Id) return Node_Sets.Set
   with
     Pre  => not Is_Wrapper_Package (E),
     Post =>
       (for all Obj of States_And_Objects'Result =>
          Ekind (Obj) in E_Abstract_State | E_Constant | E_Variable);
   --  Return objects that can appear on the LHS of the Initializes contract
   --  for a package E.

   function Conversion_Is_Move_To_Constant (Expr : Node_Id) return Boolean
   with Pre => Nkind (Expr) in N_Type_Conversion | N_Unchecked_Type_Conversion;
   --  Return True if a conversion can cause an object to be moved.
   --  Currently, we return True iff:
   --    * We are converting from an access-to-variable type to a named
   --      access-to-constant type
   --    * The prefix is not part of a constant and we are not in an assertion,
   --      otherwise this is not a move.

   function Value_Is_Never_Leaked (Expr : N_Subexpr_Id) return Boolean;
   --  Checks whether a created access value is known to never leak

   procedure Structurally_Decreases_In_Call
     (Param       : Formal_Kind_Id;
      Call        : N_Call_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  Return True if Param is a structural variant for the recursive call Call

   procedure Structurally_Decreases_In_Loop
     (Brower      : Entity_Id;
      Loop_Stmt   : N_Loop_Statement_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  Return True if Brower is a structural variant for Loop_Stmt

   procedure Register_Exception (E : E_Exception_Id);
   --  Register an exception

   function All_Exceptions return Node_Sets.Set;
   --  Get all the exceptions visible from analyzed code

   procedure Collect_Reachable_Handlers (Call_Or_Stmt : Node_Id)
   with
     Pre =>
       Nkind (Call_Or_Stmt)
       in N_Function_Call | N_Procedure_Call_Statement | N_Raise_Statement;
   --  Call_Or_Stmt shall be a call which might raise exceptions or a raise
   --  statement. Collect all the exception handlers which might be reached
   --  when jumping from Stmt and store them in a map. Also collect exceptions
   --  which might be raised by reraise statements.

   function Reachable_Handlers (Call_Or_Stmt : Node_Id) return Node_Lists.List
   with
     Pre  => Nkind (Call_Or_Stmt) in N_Subprogram_Call | N_Raise_Statement,
     Post =>
       Might_Raise_Handled_Exceptions (Call_Or_Stmt)
       /= Reachable_Handlers'Result.Is_Empty;
   --  Call_Or_Stmt shall be a call which might raise exceptions or a raise
   --  statement. Return all exception handlers which might be reached when
   --  jumping from Stmt. If the enclosing body might be exited, it will be the
   --  last elements of the list. If the statement does not raise any handled
   --  exception, the list is empty. If Call_Or_Stmt is a function called in
   --  a ghost assignment or a ghost procedure call, that occurs in non-ghost
   --  code, no exception can be handled, so the list is empty.

   function By_Copy (Obj : Formal_Kind_Id) return Boolean;
   --  Return True if Obj is known to be passed by copy. In parameters of an
   --  access-to-variable type are considered to be passed by reference in
   --  accordance to ownership principles.

   function By_Reference (Obj : Formal_Kind_Id) return Boolean;
   --  Return True if Obj is known to be passed by reference. See above.

   --  This package defines a type and operations for sets of exceptions. These
   --  sets can either be constructed from the empty set by adding elements or
   --  from the set containing all exceptions by removing them.

   package Exception_Sets is

      type Set is tagged private;

      function Exactly (E : E_Exception_Id) return Set;
      --  Return the set containing only the exception E

      function All_Exceptions return Set;
      --  Return the set containing all Ada exceptions

      procedure Disclose
        (S : Set; All_But : out Boolean; Exc_Set : out Node_Sets.Set);
      --  If All_But is True, then Exc_Set contains the exceptions which are
      --  not in the set S. Otherwise, the exception set S contains exactly the
      --  exceptions of Exc_Set.

      --  Set operations

      function Empty_Set return Set;

      function Is_Empty (S : Set) return Boolean;

      function Is_Subset (Left, Right : Set) return Boolean;

      function Contains (S : Set; E : E_Exception_Id) return Boolean;

      procedure Difference (Left : in out Set; Right : Set)
      with Post => Is_Subset (Left, Left'Old);

      procedure Exclude (S : in out Set; E : E_Exception_Id)
      with Post => not Contains (S, E);

      procedure Include (S : in out Set; E : E_Exception_Id)
      with Post => Contains (S, E);

      procedure Intersection (Left : in out Set; Right : Set)
      with Post => Is_Subset (Left, Left'Old) and Is_Subset (Left, Right);

      procedure Union (Left : in out Set; Right : Set)
      with
        Post =>
          Is_Subset (Left'Old, Left) and Is_Subset (Right, Right => Left);

      --  For display

      function Print (S : Set) return String;

   private
      type Set is tagged record
         All_But : Boolean;
         Exc_Set : Node_Sets.Set;
      end record;
   end Exception_Sets;

   function Is_Inlined_Call (Stmt : Node_Id) return Boolean
   is (Nkind (Stmt) = N_Block_Statement
       and then Present (Original_Node (Stmt))
       and then Nkind (Original_Node (Stmt)) = N_Procedure_Call_Statement);

   function Called_Entity_From_Inlined_Call (Call : Node_Id) return Entity_Id
   is (Get_Called_Entity (Original_Node (Call)))
   with Pre => Is_Inlined_Call (Call);

   function Is_Ghost_With_Respect_To_Context (Call : Node_Id) return Boolean
   with
     Pre =>
       (Call in N_Call_Id or else Is_Inlined_Call (Call))
       and then
         (if Nkind (Call) = N_Function_Call
          then Is_Function_Call_With_Side_Effects (Call));
   --  Detect if a call with side effects is ghost respectively to the
   --  enclosing calling context (the assertion level associated to the call
   --  depends on the assertion level of the calling subprogram). In
   --  particular, exceptions do not escape such calls.

   function Has_Exceptional_Contract (E : Entity_Id) return Boolean;
   --  Return True if E has an exceptional contract with cases which are not
   --  all statically False.

   function Get_Exceptions_For_Subp
     (Subp : Entity_Id) return Exception_Sets.Set;
   --  Retrieve all exceptions potentially raised by Subp

   function Get_Exceptions_From_Handler
     (N : N_Exception_Handler_Id) return Exception_Sets.Set;
   --  Retrieve all exceptions handled by a handler

   function Get_Exceptions_From_Handlers
     (N : N_Handled_Sequence_Of_Statements_Id) return Exception_Sets.Set;
   --  Retrieve all exceptions handled in a sequence of statements

   function Get_Handled_Exceptions
     (Call_Or_Stmt : Node_Id) return Exception_Sets.Set;
   --  Retrieve all exceptions either handled by a handler above Call_Or_Stmt
   --  or expected by the enclosing unit. If Call_Or_Stmt is a ghost function
   --  or procedure call occurring in non-ghost code, no exception can be
   --  handled.

   function Get_Raised_Exceptions
     (Call_Or_Stmt : Node_Id; Only_Handled : Boolean) return Exception_Sets.Set
   with
     Pre =>
       Nkind (Call_Or_Stmt)
       in N_Function_Call
        | N_Procedure_Call_Statement
        | N_Entry_Call_Statement
        | N_Raise_Statement
       and then
         (if Nkind (Call_Or_Stmt) = N_Function_Call
          then
            Is_Function_With_Side_Effects (Get_Called_Entity (Call_Or_Stmt)));
   --  Retrieve all exceptions raised by Call_Or_Stmt. If Only_Handled is True,
   --  only consider exception which are handled above Call_Or_Stmt.

   function Might_Raise_Handled_Exceptions
     (Call_Or_Stmt : Node_Id) return Boolean
   is (not Get_Raised_Exceptions (Call_Or_Stmt, True).Is_Empty);

   function Has_Program_Exit (E : Entity_Id) return Boolean;
   --  Return True if E has a program exit postcondition which is not
   --  statically False or if it has an Exit_Cases contract with at least one
   --  Program_Exit case.

   function Get_Program_Exit (E : Entity_Id) return Node_Id
   with Pre => Has_Program_Exit (E);
   --  Return E's program exit postcondition or Empty if there is none.

   function Might_Exit_Program (Call : Node_Id) return Boolean
   with Pre => Nkind (Call) in N_Subprogram_Call | N_Entry_Call_Statement;
   --  Return True if Call might exit the whole program in a way expected by
   --  the enclosing unit.

   function Is_Potentially_Invalid (E : Entity_Id) return Boolean;
   --  Return True if E is subject to a Potentially_Invalid aspect and it might
   --  have invalid values.

   function Is_Potentially_Invalid_Expr (Expr : Node_Id) return Boolean;
   --  Return True if Expr might be invalid. It might happen for:
   --  * Potentially invalid or locally potentially invalid objects,
   --  * Reference to the 'Result attribute of a function potentially invalid
   --    function,
   --  * Call to a potentially invalid function, and
   --  * References to 'Old and 'Loop_Entry if the prefix is not a scalar and
   --    might be invalid.
   --  Other expressions require a validity check.

   function Propagates_Validity_Flag (N : Node_Id) return Boolean;
   --  Returns True on an assignment statement, an object declaration, or
   --  an actual parameter of mode IN OUT or OUT that propagates the invalidity
   --  flag of its source to its target. Otherwise, a validity check should
   --  be issued.

   procedure Iter_Exited_Scopes_Ignore_Stops
     (Destination : Node_Id;
      Exc_Set     : Exception_Sets.Set;
      Is_Continue : Boolean)
   is null;

   generic
      with procedure Process (Scop : Node_Id);
      with
        procedure Stop
          (Destination : Node_Id;
           Exc_Set     : Exception_Sets.Set;
           Is_Continue : Boolean) is Iter_Exited_Scopes_Ignore_Stops;
   procedure Iter_Exited_Scopes_With_Specified_Transfer
     (Start             : Node_Id;
      Goto_Labels       : Node_Sets.Set := Node_Sets.Empty_Set;
      Exception_Sources : Exception_Sets.Set := Exception_Sets.Empty_Set;
      Exited_Loops      : Node_Sets.Set := Node_Sets.Empty_Set;
      Continued_Loops   : Node_Sets.Set := Node_Sets.Empty_Set;
      Return_Source     : Boolean := False);
   --  For Start a statement that can be exited by indirect transfer of
   --  control, iterates over scopes exited upon such indirect transfer.
   --  Defaulted parameters list the potential indirect transfer of control we
   --  may be using to exit the current node.
   --  * Goto_Labels corresponds to (goto L) sources. It provides the intended
   --    set of target labels.
   --  * Exception_Sources correspond to exception-raising sources. It provides
   --    the expected set of exceptions.
   --  * Exited_Loops corresponds to exit statement sources. It provides the
   --    loops that are exited by such statements.
   --  * Continued_Loops corresponds to continue statement sources. It provides
   --    the loops whose iterations are completed by such statements.
   --  * Return_Source corresponds to (extended) return statement. Note that
   --    return statements nested within extended return statements do not exit
   --    the full body, instead they jump to the completion of the enclosing
   --    extended return statement.
   --
   --  The iteration calls Process over each of the scopes exactly once, in
   --  order from innermost to outermost. Here, scopes are considered to be
   --  constructs to which finalization activities may be attached. These can
   --  be
   --  * Block statements, for their declarations
   --  * Extended return statements, for their one declarations. This is not
   --    exited by inner return, nor by the extended return statement itself.
   --  * For loop statements, for their declared index
   --  * Entity with a body, for the declarations at the start of the body
   --  * Handled sequence of statements, for the finally statements
   --
   --  The distinct possibilities may stop exiting scopes at different levels.
   --  Stop is called once per reached destination, after all relevant scopes
   --  have been exited and no other. The arguments passed to Stop may be:
   --  * Goto label entities (targets of goto)
   --  * Loop statements (targets of loop exit, or of loop continues).
   --    Is_Continue is set to true if and only if the destination is that
   --    of the loop continue (the end of the iteration rather than the loop).
   --  * Extended return statements (targets of inner return statements)
   --  * Exception handler. In this case, Exc_Sets contains the (non-empty)
   --    subset of exceptions that may reach the handler.
   --  * Entity with a body, corresponding to exiting the body. In this case,
   --    Exc_Set is empty for normal return, and non-empty for exceptional
   --    exit.
   --
   --  Note that calling Iter_Exited_Scopes_With_Specified_Transfer over
   --  Transfer-of-control that do not (or cannot) arise within Start is safe.
   --  Transfer-of-control that cannot target any destination in the enclosing
   --  scopes (which includes exceptional contract for exceptions) are ignored.
   --  As such, the last call to Process/Stop is always a meaningful call to
   --  Stop.

   generic
      with procedure Process (Scop : Node_Id);
      with
        procedure Stop
          (Destination : Node_Id;
           Exc_Set     : Exception_Sets.Set;
           Is_Continue : Boolean) is Iter_Exited_Scopes_Ignore_Stops;
   procedure Iter_Exited_Scopes (Source : Node_Id)
   with
     Pre =>
       Nkind (Source)
       in N_Subprogram_Call
        | N_Entry_Call_Statement
        | N_Raise_Statement
        | N_Goto_Statement
        | N_Exit_Statement
        | N_Continue_Statement
        | N_Simple_Return_Statement
        | N_Extended_Return_Statement
       and then
         (if Nkind (Source) = N_Function_Call
          then Is_Function_With_Side_Effects (Get_Called_Entity (Source)));
   --  Wrapper over Iter_Exited_Scopes_With_Specified_Transfer covering the
   --  most common cases. For Source a statement potentially causing indirect
   --  transfer of control, call Iter_Exited_Scopes_With_Specified_Transfer
   --  with the transfer of control potentially generated by the source.

   -----------------------------------------------
   --  Control-flow graph of statements/bodies  --
   -----------------------------------------------

   package Local_CFG is

      --  For each statement/subprogram body B,
      --  there is an implicit control-flow graph (CFG) maintained for B,
      --  the local graph of B, corresponding to control paths that
      --  remain within B. The vertices of the local graph of B represent the
      --  basic 'instructions' of B (possibly no-ops), and the edges represent
      --  the potential transfer-of-control between them. Edges are unlabelled.
      --
      --  The locals graph are only available after marking.
      --
      --  Local graphs share their vertices and edges, in the sense that
      --  * Vertices of a statement's local graph are vertices of local graphs
      --    of enclosing statements/the enclosing body (not skipping
      --    across bodies)
      --  * If two vertices have an edge between them in some local CFG,
      --    then they have the same edge in any local CFG for which they
      --    are vertices.
      --  In other words, each local graph is simply the restriction of
      --  the enclosing body's CFG to the vertices of the enclosed
      --  construct.
      --
      --  The local CFG do not go through the bodies of nested packages,
      --  relying on Ada+SPARK assumptions that make them side-effect free.

      subtype Graph_Id is Node_Id
      with
        Predicate =>
          Nkind (Graph_Id)
          in N_Statement_Other_Than_Procedure_Call
           | N_Procedure_Call_Statement
           | N_Entity;
      --  Local Graphs are indexed by nodes which are either statements
      --  or entities that have body.

      subtype Has_Finalization is Node_Id
      with
        Predicate =>
          (declare
             N : constant Node_Id := Has_Finalization;
           begin
             Nkind (N) = N_Handled_Sequence_Of_Statements
             and then Present (Finally_Statements (N)));
      --  Construct with potentially attached finalization activities tracked
      --  in the graph. Currently, only finally sections are tracked as they
      --  are the only effectful ones. End-of-borrowing is treated like a
      --  finalization in proof, but has essentially no side-effect, so we do
      --  not need to track it explicitly.

      type Vertex_Kind is
        (Entrance,
         Completion,
         Loop_Cond,
         Loop_Iter,
         Body_Exit,
         Final_Entrance,
         Final_Completion);
      --  Vertex kinds that can occur in the graph. The execution behavior
      --  can be thought as being attached to outgoing edges.
      --  * Entrance vertices: corresponds to the execution at the start of
      --    a construct. For the vast majority of the construct, this is the
      --    only vertex associated with the construct.
      --    There is also an Entrance vertex for entities with a body,
      --    corresponding to the entry point.
      --  * Completion vertices: corresponds to the regular completion of
      --    a construct. This is only present for non-loop statements
      --    which may have attached finalization activities, that is:
      --    + Handled sequence of statements, due to potential explicit finally
      --      The completion vertex corresponds to regular completion of the
      --      main sequence, this does not cover completion of individual
      --      handlers and precedes the finally block if any.
      --    + Anything that might have attached declarations
      --      - Block statements
      --      - Extended return statements
      --      - Entity body
      --    Loop statements are treated separately.
      --  * Loop vertices: The structure of a loop is as follow:
      --    + Entrance: the initialization, before the loop starts.
      --      Performs initialization of any (implicit) constant values
      --      needed for iteration (example: evaluation of loop bounds,
      --      or of Loop_Entry references), and initializing any implicit
      --      loop cursor. This goes to Loop_Cond.
      --    + Loop_Cond: the condition, the first vertex of the actual loop,
      --      right after initialization. Corresponds to declaring
      --      the loop index if any (a constant) and testing the exit
      --      condition. This is also the vertex at which the loop may instead
      --      complete, in case the condition fails. As such, a Completion
      --      vertex would be redundant.
      --    + Loop_Iter: the iteration, the last vertex of the actual loop,
      --      right before returning to Loop_Cond. Corresponds to
      --      regular completion of the loop statements, right before loop
      --      cursor (if any) is increased. This can be thought as the
      --      Completion vertex for the loop body.
      --    The loop body is made up by vertices of internal statements.
      --  * Sink vertices (Body_Exit):
      --    those corresponds to the exit paths of a body.
      --    All exit paths (regular and exceptionals) are merged together.
      --    Body_Exit comes after everything associated to the body is done.
      --    In particular, it is posterior to the body's completion vertex.
      --  * Finalization interface vertices (Final_Entrance,Final_Completion)
      --    Corresponds to entrance and regular completion vertices for a
      --    a finalization subgraph. This currently cover only finally
      --    sections.

      type Vertex is record
         Kind : Vertex_Kind;
         Node : Node_Id;
      end record
      with
        Predicate =>
          (case Vertex.Kind is
             when Entrance                          => True,
             when Completion                        =>
               Nkind (Vertex.Node)
               in N_Block_Statement
                | N_Handled_Sequence_Of_Statements
                | N_Extended_Return_Statement
                | N_Entity,
             when Loop_Cond | Loop_Iter             =>
               Vertex.Node in N_Loop_Statement_Id,
             when Body_Exit                         =>
               Nkind (Vertex.Node) in N_Entity,
             when Final_Entrance | Final_Completion =>
               Vertex.Node in Has_Finalization);

      function Starting_Vertex (N : Node_Id) return Vertex
      is (Kind => Entrance, Node => N);
      --  Get starting vertex of construct/entity.
      --  For nodes which are not Graph_Id (e.g local declarations),
      --  this is the (plain) individual vertex corresponding to the node.
      --  For nodes which do not have a matching graph (e.g local
      --  declarations), this is the only individual vertex corresponding to
      --  the node.

      function Vertex_Hash (X : Vertex) return Ada.Containers.Hash_Type;

      package Vertex_Sets is new
        Ada.Containers.Hashed_Sets
          (Element_Type        => Vertex,
           Hash                => Vertex_Hash,
           Equivalent_Elements => "=");

      function True_On_Every_Vertex (Dummy : Vertex) return Boolean
      is (True);

      procedure Collect_Vertices_Leading_To
        (Graph       : Graph_Id;
         Targets     : in out Vertex_Sets.Set;
         Pred        : not null access function (V : Vertex) return Boolean :=
           True_On_Every_Vertex'Access;
         Empty_Paths : Boolean := True);
      --  For a set of targets within Graph's local CFG,
      --  the initial content of Targets, replace Targets with the set of
      --  vertices such that there is a path within Graph's local CFG that
      --  reaches a target, and such that the source vertex of every edge in
      --  the path satisfies Pred. Empty paths (paths with no edges) are
      --  allowed iff Empty_Paths is True (in which case all targets
      --  must necessarily be kept in Targets).

   end Local_CFG;

end SPARK_Util;
