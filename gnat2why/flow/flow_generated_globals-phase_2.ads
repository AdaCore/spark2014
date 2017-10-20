------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2014-2017, Altran UK Limited                 --
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
with Sinfo;                              use Sinfo;
with SPARK_Definition;                   use SPARK_Definition;
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

   package Name_Nat is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Nat,
      Hash            => Name_Hash,
      Equivalent_Keys => "=");

   Task_Instances : Task_Instances_Maps.Map;
   --  Task instances

   Max_Queue_Length_Map : Name_Nat.Map;
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

   function Refinement_Exists (AS : Entity_Id) return Boolean
   with Pre => Ekind (AS) = E_Abstract_State;
   --  Returns True iff a refinement has been specified for abstract state AS

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

   function GG_Encapsulating_State (EN : Entity_Name) return Any_Entity_Name
   with Pre => GG_State_Constituents_Map_Is_Ready;
   --  Returns the Entity_Name of the directly encapsulating state. If one does
   --  not exist it returns Null_Entity_Name.

   procedure GG_Get_Globals (E           : Entity_Id;
                             S           : Flow_Scope;
                             Globals : out Global_Flow_Ids)
   with Pre  => GG_Mode = GG_Read_Mode and then
                Ekind (E) in E_Entry     |
                             E_Function  |
                             E_Procedure |
                             E_Task_Type,
        Post => GG_Mode = GG_Read_Mode;
   --  Determines the set of all globals

   function GG_Get_State_Abstractions return Name_Sets.Set
   with Pre => GG_State_Constituents_Map_Is_Ready;
   --  @return a set of Entity_Names with all the state abstractions
   --    that the Generated Globals know of.

   function GG_Get_Initializes
     (E : Entity_Id;
      S : Flow_Scope)
      return Dependency_Maps.Map
   with Pre => GG_Has_Been_Generated and then
               Ekind (E) = E_Package;
   --  @param E is the package whose generated Initializes aspect we want
   --  @param S is the Flow_Scope at which we need to up project the results
   --  @return the generated initializes if it exists or an empty dependency
   --    map otherwise.

   function GG_Get_Local_Variables
     (E : Entity_Id)
      return Name_Sets.Set
   with Pre => GG_Has_Been_Generated and then
               Ekind (E) in E_Package;
   --  This function takes as a parameter a package entity and returns a
   --  set of names comprising:
   --    * all variables declared directly inside the package,
   --    * variables declared in the private part of nested packages that are
   --      in SPARK and do NOT have a user-provided Initializes aspect and
   --    * variables introduced in the declarations of the body part of nested
   --      packages that are in SPARK and do NOT have a user-provided
   --      Abstract_State aspect.
   --  Constants with variable inputs are also included in the above.
   --
   --  @param E is the entity whose local variables we are asking for
   --  @return the set of Entity_Names of the local variables as recorded
   --    by the generated globals

   function GG_Is_Initialized_At_Elaboration (EN : Entity_Name) return Boolean
   with Pre => GG_Has_Been_Generated;
   --  @param EN is the entity name we want to check
   --  @return True iff EN is initialized at elaboration

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

   function Is_Potentially_Blocking (E : Entity_Id) return Boolean
   with Pre => GG_Has_Been_Generated and then
               Analysis_Requested (E, With_Inlined => True) and then
               Ekind (E) in E_Entry | E_Procedure | E_Function;
   --  Returns True if subprogram E is potentially blocking or its blocking
   --  status is unknown; returns False if it is known to be nonblocking.

   function Is_Recursive (E : Entity_Id) return Boolean
   with Pre => GG_Has_Been_Generated and then
               Ekind (E) in E_Entry | E_Procedure | E_Function;
   --  Returns True iff subprogram E calls (directly or indirectly) itself,
   --  i.e. is a recursive subprogram.

   function Calls_Current_Task (E : Entity_Id) return Boolean
   with Pre => GG_Has_Been_Generated and then
               Analysis_Requested (E, With_Inlined => True) and then
               (Ekind (E) = E_Entry or else
                (Ekind (E) = E_Procedure and then Is_Interrupt_Handler (E)));
   --  Returns True iff subprogram E calls (directly or indirectly) function
   --  Ada.Task_Identification.Current_Task.

   function Get_Constituents (E : Entity_Name) return Name_Sets.Set;
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
   --  @param Ent an entity name that refers to a task, main-like subprogram or
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

end Flow_Generated_Globals.Phase_2;
