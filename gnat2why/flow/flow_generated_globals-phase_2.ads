------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2014-2020, Altran UK Limited                --
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

with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Ordered_Multisets;
with Flow_Dependency_Maps;               use Flow_Dependency_Maps;
with Lib;                                use Lib;
with Sinfo;                              use Sinfo;
with Snames;                             use Snames;
with SPARK_Definition;                   use SPARK_Definition;
with SPARK_Util;                         use SPARK_Util;
with SPARK_Util.Subprograms;             use SPARK_Util.Subprograms;

package Flow_Generated_Globals.Phase_2 is

   function "<" (Left, Right : Task_Object) return Boolean;
   --  Compare task objects giving preference to the object from the current
   --  compilation unit, or else, visible by Entity_Id, or else, resort to the
   --  alphabetic order of object names.

   package Task_Multisets is
     new Ada.Containers.Ordered_Multisets (Element_Type => Task_Object,
                                           "<"          => "<",
                                           "="          => "=");
   --  Containers with instances of a task type; mulisets (i.e. ordered bags)
   --  are needed because a record object whose components have the same task
   --  type is represented by multiple task instances. Perhaps this is not
   --  elegant, but is a result of code evolution; changing it now would
   --  complicate phase 1 and perhaps we want to use it for component-wise
   --  error location in the future.

   package Task_Instances_Maps is
     new Ada.Containers.Hashed_Maps (Key_Type        => Entity_Name,
                                     Element_Type    => Task_Multisets.Set,
                                     Hash            => Name_Hash,
                                     Equivalent_Keys => "=",
                                     "="             => Task_Multisets."=");
   --  Containers that map task types to objects with task instances (e.g. task
   --  arrays may contain several instances of a task type and task record may
   --  contain instances of several tasks).

   package Max_Queue_Lenghts_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Nat,
      Hash            => Name_Hash,
      Equivalent_Keys => "=");

   Task_Instances : Task_Instances_Maps.Map;
   --  Task instances

   Max_Queue_Lengths : Max_Queue_Lenghts_Maps.Map;
   --  Maps entries to their Max_Queue_Length

   -------------------------
   -- Reading & Computing --
   -------------------------

   procedure GG_Read (GNAT_Root : Node_Id)
   with Pre  => GG_Mode = GG_No_Mode
                and then Nkind (GNAT_Root) = N_Compilation_Unit,
        Post => GG_Mode = GG_Read_Mode;
   --  Reads all ALI files and produce the transitive closure

   --------------
   -- Querying --
   --------------

   function Find_In_Refinement (AS : Entity_Id; C : Entity_Id) return Boolean
   with Pre => Ekind (AS) = E_Abstract_State
                 and then
               Ekind (C) in E_Abstract_State | E_Constant | E_Variable
                 and then
               Refinement_Exists (AS);
   --  Returns True iff constituent C is mentioned in the refinement of the
   --  abstract state AS.

   function GG_Has_Been_Generated return Boolean;
   --  Checks if the Globals Graph has been generated
   --  @return True iff the Globals Graph has been generated

   function GG_State_Constituents_Map_Is_Ready return Boolean
   with Ghost;
   --  Returns True iff the mapping between abstract states and their
   --  constituents have been populated.

   function GG_Is_Constituent (EN : Entity_Name) return Boolean
   with Pre => GG_State_Constituents_Map_Is_Ready;
   --  Returns true iff E is a constituent of some state abstraction
   --  that we loaded while reading the ALI files.

   function GG_Is_Part_Of_Constituent (EN : Entity_Name) return Boolean
   with Pre => GG_State_Constituents_Map_Is_Ready;
   --  Returns true iff E is a Part_Of constituent of some state abstraction
   --  that we loaded while reading the ALI files.

   function GG_Encapsulating_State (EN : Entity_Name) return Any_Entity_Name
   with Pre => GG_State_Constituents_Map_Is_Ready;
   --  Returns the Entity_Name of the directly encapsulating state. If one does
   --  not exist it returns Null_Entity_Name.

   procedure GG_Get_Globals (E       : Entity_Id;
                             S       : Flow_Scope;
                             Globals : out Global_Flow_Ids)
   with Pre  => GG_Mode = GG_Read_Mode and then
                Ekind (E) in E_Entry     |
                             E_Function  |
                             E_Package   |
                             E_Procedure |
                             E_Task_Type,
        Post => GG_Mode = GG_Read_Mode;
   --  Determines the set of all globals

   function GG_Is_Abstract_State (EN : Entity_Name) return Boolean
   with Pre => GG_State_Constituents_Map_Is_Ready;
   --  @return true iff EN denotes an abstract state

   function Refinement_Exists (AS : Entity_Id) return Boolean
   with Pre => Ekind (AS) = E_Abstract_State;
   --  Returns True iff a refinement has been specified for abstract state AS

   function Expand_Abstract_State (F : Flow_Id) return Flow_Id_Sets.Set
   with Post => (for all E of Expand_Abstract_State'Result =>
                    Is_Entire_Variable (E) and then E.Variant = Normal_Use);
   --  If F represents abstract state, return the set of all its components.
   --  Otherwise return F.

   function GG_Get_Initializes (E : Entity_Id) return Dependency_Maps.Map
   with Pre => GG_Has_Been_Generated and then
               Ekind (E) = E_Package and then
               No (Get_Pragma (E, Pragma_Initializes));
   --  @param E is the package whose generated Initializes aspect we want

   function GG_Get_Local_Variables (E : Entity_Id) return Node_Sets.Set
   with Pre  => GG_Has_Been_Generated and then
                Ekind (E) = E_Package and then
                Is_In_Analyzed_Files (E),
        Post => (for all Var of GG_Get_Local_Variables'Result =>
                    Ekind (Var) in E_Abstract_State | E_Constant | E_Variable
                    and then not Is_Internal (Var));
   --  @param E is the package whose local variables we are asking for
   --  @return objects that may appear on the LHS of an Initializes contract

   function GG_Is_Initialized_At_Elaboration (EN : Entity_Name) return Boolean
   with Pre => GG_Has_Been_Generated;
   --  @param EN is the entity name we want to check
   --  @return True iff EN is initialized at elaboration

   function GG_Is_Ghost_Entity (EN : Entity_Name) return Boolean
   with Pre => GG_Has_Been_Generated;
   --  @param EN is the entity name that we check for being a ghost entity
   --  @return True iff EN is a ghost entity

   function GG_Is_Constant (EN : Entity_Name) return Boolean
   with Pre => GG_Has_Been_Generated;
   --  @param EN is the entity name that we check for being a constant
   --  @return True iff EN is a constant

   function GG_Is_CAE_Entity (EN : Entity_Name) return Boolean
   with Pre => GG_Has_Been_Generated;
   --  @param EN is the entity name that we check for being a constant after
   --    elaboration.
   --  @return True iff EN is a constant after elaboration

   function GG_Is_Volatile (EN : Entity_Name) return Boolean
   with Pre => GG_Has_Been_Generated;
   --  @param EN is the entity name that we check for being volatile
   --  @return True iff EN is volatile

   function GG_Has_Async_Writers (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Async_Writers'Result
                 then GG_Is_Volatile (EN));
   --  @param EN is the entity name that we check for having Async_Writers
   --  @return True iff EN has Async_Writers set

   function GG_Has_Async_Readers (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Async_Readers'Result
                 then GG_Is_Volatile (EN));
   --  @param EN is the entity name that we check for having Async_Readers
   --  @return True iff EN has Async_Readers set

   function GG_Has_Effective_Reads (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Effective_Reads'Result
                 then GG_Has_Async_Writers (EN));
   --  @param EN is the entity name that we check for having Effective_Reads
   --  @return True iff EN has Effective_Reads set

   function GG_Has_Effective_Writes (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Effective_Writes'Result
                 then GG_Has_Async_Readers (EN));
   --  @param EN is the entity name that we check for having Effective_Writes
   --  @return True iff EN has Effective_Writes set

   function Generated_Calls (E : Entity_Id) return Node_Lists.List
   with Pre  => GG_Has_Been_Generated and then
                Analysis_Requested (E, With_Inlined => True) and then
                Ekind (E) in Entry_Kind
                           | E_Function
                           | E_Package
                           | E_Procedure
                           | E_Task_Type,
        Post => (for all Callee of Generated_Calls'Result
                   => Ekind (Callee) in Entry_Kind
                                      | E_Function
                                      | E_Package
                                      | E_Procedure);
   --  Returns callees of entity E

   function Has_Potentially_Blocking_Statement (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Function | E_Procedure | E_Package;
   --  Returns True iff E has a potentially blocking statement (or if its
   --  blocking status is unknown, e.g. when the body is not in SPARK).
   --
   --  Note: it returns False when E is potentially blocking due to a call to
   --  a potentially blocking subprogram.

   function Potentially_Blocking_Callee (E : Entity_Id) return Any_Entity_Name
   with Pre => Ekind (E) in E_Function | E_Procedure | E_Package;
   --  Returns an Entity_Name of a potentially blocking callee, if any, and
   --  Null_Entity_Name if none such a callee exists.

   type External_Call is record
      Protected_Subprogram : Entity_Id;
      External_Callee      : Any_Entity_Name;
   end record
   with Dynamic_Predicate =>
     (Present (Protected_Subprogram) = (External_Callee in Entity_Name));
   --  Represents an external call on the same target as that of a protected
   --  action; if no such an call exists, then its components are left as
   --  Empty and Null_Entity_Name. It is needed for detailed messages about
   --  potentially blocking operations.

   function Potentially_Blocking_External_Call
     (E       : Entity_Id;
      Context : Entity_Id)
      return External_Call
   with Pre  => GG_Has_Been_Generated
                and then Ekind (E) in E_Procedure | E_Function | E_Package
                and then not In_Predefined_Unit (E)
                and then Ekind (Context) = E_Protected_Type;
   --  Returns a detailed info about an external call on the same target as
   --  that of a protected action, if such a call exists.

   function Is_Recursive (E : Entity_Id) return Boolean
   with Pre => GG_Has_Been_Generated and then
               Ekind (E) in E_Entry | E_Procedure | E_Function;
   --  Returns True iff subprogram E calls (directly or indirectly) itself,
   --  i.e. is a recursive subprogram.

   function Mutually_Recursive (E1, E2 : Entity_Id) return Boolean
   with Pre => GG_Has_Been_Generated and then
               Ekind (E1) in E_Entry | E_Procedure | E_Function and then
               Ekind (E2) in E_Entry | E_Procedure | E_Function;
   --  Returns True iff subprogram E1 calls (directly or indirectly) E2, and
   --  conversly, i.e. they are mutually recursive subprograms.

   function Calls_Current_Task (E : Entity_Id) return Boolean
   with Pre => GG_Has_Been_Generated and then
               Analysis_Requested (E, With_Inlined => True) and then
               (Ekind (E) = E_Entry or else
                (Ekind (E) = E_Procedure and then Is_Interrupt_Handler (E)));
   --  Returns True iff subprogram E calls (directly or indirectly) function
   --  Ada.Task_Identification.Current_Task.

   function Get_Constituents (E : Entity_Name) return Name_Sets.Set
   with Pre => GG_Is_Abstract_State (E);
   --  Returns the constituents for abstract state E

   function Is_Potentially_Nonreturning_Internal (E : Entity_Id)
                                                  return Boolean
   with Pre => GG_Has_Been_Generated and then
               Entity_In_SPARK (E) and then
               Ekind (E) in E_Entry     |
                            E_Procedure |
                            E_Function;
   --  Returns True iff subprogram E is potentially nonreturning, i.e.
   --  * is a procedure annotated with pragma No_Return
   --  * contains possibly nonterminating loops
   --  * is recursive
   --  * calls a potentially nonreturning subprogram.
   --
   --  It does not take into account the Terminating annotation for subprogram
   --  E which is taken into account by the function
   --  Is_Potentially_Nonreturning.
   --
   --  This function relies on the work carried on in phase 1 where we register
   --  a subprogram as nonreturning if:
   --    - contains possibily nonterminating loops
   --    - it is annotated with No_Return
   --    - calls predefined procedures annotated with No_Return
   --    - has its body not in SPARK.
   --
   --    The case of a subprogram with body not SPARK needs a closer look. In
   --    fact we will need to look at calls that might come from its contracts.
   --    In particular:
   --    1) if a subprogram does not have a body yet (no .adb) then
   --       - if it does not call any subprogram in its contracts we assume it
   --         to terminate
   --       - if it does call subprograms which are nonreturning then we assume
   --         it to be nonreturning
   --       - if it does call subprograms which are returning then we assume it
   --         to terminate.
   --    2) if a subprogram is Intrinsic or Imported we can apply the same
   --       reasoning described above.
   --    3) if a subprogram has a body and this is not in SPARK then we always
   --       assume it to be nonreturning.
   --    4) if a subprogram is in a generic predefined unit then:
   --       - if the generic is instantiated with returning subprograms, we
   --         consider it to be returning
   --       - if the generic is instantiated with nonreturning subprograms, we
   --         consider it to be nonreturning.

   function Is_Potentially_Nonreturning (E : Entity_Id) return Boolean
   with Pre => GG_Has_Been_Generated and then
               Entity_In_SPARK (E) and then
               Ekind (E) in E_Entry     |
                            E_Procedure |
                            E_Function;
   --  Returns True iff E is not annotated as terminating and is indeed
   --  (potentially) nonreturning for some reason.
   --
   --  Note: if a subprogram is annotated as terminating then we trust that it
   --  indeed terminates when called from other subprograms. If our analysis
   --  thinks otherwise, we will issue a message but still trust the
   --  user-provided annotation.

   function Tasking_Objects
     (Kind : Tasking_Owning_Kind;
      Subp : Entity_Name)
      return Name_Sets.Set
   with Pre => GG_Has_Been_Generated;
   --  Returns the set of objects (e.g. suspension objects or entries,
   --  depending on the Kind) accessed by a main-like subprogram Subp.

   function Directly_Called_Protected_Objects
     (E : Entity_Id) return Name_Sets.Set
   with Pre => GG_Has_Been_Generated and then
               Analysis_Requested (E, With_Inlined => True);
   --  @param E an entity name that refers to a task, main-like subprogram or
   --    protected operation
   --  @return the set of protected operations that are called "directly", that
   --    is without going through other protected operations

   package Object_Priority_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Element_Type => Priority_Value);
   --  Containers with priorities of protected components

   function Component_Priorities
     (Obj : Entity_Name)
      return Object_Priority_Lists.List
   with
     Post => not Object_Priority_Lists.Is_Empty (Component_Priorities'Result);
   --  @param Obj an entity name that refers to a library-level object with
   --    protected components
   --  @return priorities of protected object components

   function GG_Has_Globals (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Entry | E_Function | E_Procedure;
   --  Return True iff the Global contract of E was recorded in phase 1

end Flow_Generated_Globals.Phase_2;
