------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 1        --
--                                                                          --
--                                 B o d y                                  --
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

with Ada.Strings.Unbounded;

with Lib.Util;                use Lib.Util;
with Osint.C;                 use Osint.C;
with Sem_Aux;                 use Sem_Aux;
with Sem_Util;                use Sem_Util;
with Snames;                  use Snames;

with Common_Iterators;        use Common_Iterators;
with SPARK_Frame_Conditions;  use SPARK_Frame_Conditions;
with SPARK2014VSN;            use SPARK2014VSN;

with Flow_Generated_Globals.ALI_Serialization;
use Flow_Generated_Globals.ALI_Serialization;
with Serialisation;           use Serialisation;

package body Flow_Generated_Globals.Phase_1 is

   package Protected_Instances_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Object_Priority);
   --  Containers with variables that contain instances of protected types; for
   --  priority ceiling checks.

   Protected_Instances : Protected_Instances_Lists.List;
   --  Instances of protected types and their static priorities

   type Task_Instance is record
      Type_Name : Entity_Name;
      Object    : Task_Object;
   end record;

   package Task_Instances_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Task_Instance);
   --  Containers with variables that contain instances of task types

   Task_Instances : Task_Instances_Lists.List;
   --  Instances of task types

   Entity_Infos : Partial_Contract_Lists.List;
   --  Entity-specific information as discovered by their analysis
   --
   --  ??? we keep this locally only because in the ALI file we first want to
   --  have entity-independent info; perhaps we do not care and can safely
   --  dump information locally for each scope.

   type Entry_With_Max_Queue_Length is record
      Entry_Name       : Entity_Name;
      Max_Queue_Length : Nat;
   end record;

   package Entries_Max_Queue_Length_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Entry_With_Max_Queue_Length);

   Entries_Max_Queue_Length : Entries_Max_Queue_Length_Lists.List;

   type Abstract_State_Constituents is record
      State        : Entity_Name;
      Constituents : Name_Lists.List;
   end record;

   package Abstract_State_Constituents_Lists is new
     Ada.Containers.Doubly_Linked_Lists
       (Element_Type => Abstract_State_Constituents);

   State_Constituents : Abstract_State_Constituents_Lists.List;
   --  List of abstract states and their constituents, i.e.
   --  abstract_state . {constituents}.

   Current_Lib_Unit : Entity_Id;
   --  Unique identifier of the top-level entity of the current library unit;
   --  it is the same for the main compilation unit and its subunits (which are
   --  processed in the same invocation of gnat2why).

   Remote_States : Name_Sets.Set;
   --  State abstractions referenced in the current compilation unit but
   --  declared outside of it.

   Predefined_Initialized_Variables : Name_Sets.Set;
   --  Variables in predefined units that are known to be initialized. We
   --  attach them to units where they are used as inputs or proof_ins, because
   --  in phase 2 we might only know them by Entity_Name (which is not enough
   --  to decide their initialization status).

   type Call_Info is record
      Caller  : Entity_Name;
      Callees : Name_Lists.List;
   end record;

   package Call_Info_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Call_Info);

   Direct_Calls_List : Call_Info_Lists.List;
   --  Container with direct calls for subprograms, entries and tasks types

   Constant_Calls_List : Call_Info_Lists.List;
   --  Calls from constants to subprograms (from other compilation units) in
   --  their initialization expressions.

   ----------------------------------------------------------------------
   --  Volatile information
   ----------------------------------------------------------------------

   Async_Writers_Vars    : Name_Sets.Set;
   Async_Readers_Vars    : Name_Sets.Set;
   Effective_Reads_Vars  : Name_Sets.Set;
   Effective_Writes_Vars : Name_Sets.Set;
   --  Volatile information

   procedure Register_Volatile (E : Entity_Id);
   --  Process E and adds it to Async_Writers_Vars, Async_Readers_Vars,
   --  Effective_Reads_Vars, or Effective_Writes_Vars as appropriate.

   --------------------------------
   -- GG_Register_Constant_Calls --
   --------------------------------

   procedure GG_Register_Constant_Calls
     (E     : Entity_Id;
      Calls : Node_Lists.List)
   is
   begin
      Constant_Calls_List.Append ((Caller  => To_Entity_Name (E),
                                   Callees => <>));

      declare
         Callees : Name_Lists.List renames
           Constant_Calls_List (Constant_Calls_List.Last).Callees;

      begin
         for Call of Calls loop
            Callees.Append (To_Entity_Name (Call));
         end loop;
      end;

   end GG_Register_Constant_Calls;

   ------------------------------
   -- GG_Register_Direct_Calls --
   ------------------------------

   procedure GG_Register_Direct_Calls (E : Entity_Id; Calls : Node_Sets.Set) is
   begin
      Direct_Calls_List.Append ((Caller  => To_Entity_Name (E),
                                 Callees => <>));

      declare
         Callees : Name_Lists.List renames
           Direct_Calls_List (Direct_Calls_List.Last).Callees;

      begin
         for Call of Calls loop
            --  Generic actual subprograms should not appear in direct calls,
            --  except for default subprograms. They are either null procedures
            --  or functions that wrap arbitrary expressions.
            pragma Assert
              (if Is_Subprogram (Call)
                 and then Is_Generic_Actual_Subprogram (Call)
               then
                 (case Ekind (Call) is
                     when E_Procedure =>
                        Null_Present (Subprogram_Specification (Call)),
                     when E_Function =>
                        True,
                     when others =>
                        raise Program_Error));

            Callees.Append (To_Entity_Name (Call));
         end loop;
      end;
   end GG_Register_Direct_Calls;

   -----------------------------
   -- GG_Register_Global_Info --
   -----------------------------

   procedure GG_Register_Global_Info (GI : Partial_Contract) is

      procedure Process_Volatiles_And_States
        (Names      : Name_Sets.Set;
         Local_Vars : Boolean := False);
      --  Goes through Names, finds volatiles and remote states and stores them
      --  in the appropriate containers. Local_Vars should be set to true when
      --  processing local variables for a run-time check that they do not
      --  represent remote states.

      procedure Process_Predefined_Variables (Names : Name_Sets.Set);
      --  Similarly to registering so called "remote states", i.e. states that
      --  are pulled from other compilation units and might only be known by
      --  Entity_Name in phase 2, we need to register variables in predefined
      --  units to know their initialization status.
      --
      --  ??? this routine repeats conversion from Entity_Name to Entity_Id,
      --  which is already done in Process_Volatiles_And_States; however, those
      --  conversion will be eliminated by rewriting front-end globals to
      --  work on Entity_Id, not by refactoring those two routines.

      ----------------------------------
      -- Process_Predefined_Variables --
      ----------------------------------

      procedure Process_Predefined_Variables (Names : Name_Sets.Set) is
      begin
         for Name of Names loop
            declare
               E : constant Entity_Id := Find_Entity (Name);
            begin
               --  Convert name back to Entity_Id; this should work for
               --  everything except the special __HEAP name that represent a
               --  non-existing heap entity.
               if Present (E)
                 and then Is_Predefined_Initialized_Variable (E)
               then
                  Predefined_Initialized_Variables.Include (Name);
               end if;
            end;
         end loop;
      end Process_Predefined_Variables;

      ----------------------------------
      -- Process_Volatiles_And_States --
      ----------------------------------

      procedure Process_Volatiles_And_States
        (Names      : Name_Sets.Set;
         Local_Vars : Boolean := False) is
      begin
         for Name of Names loop
            declare
               E : constant Entity_Id := Find_Entity (Name);
            begin
               --  Convert name back to Entity_Id; this should work for
               --  everything except the special __HEAP name that represent a
               --  non-existing heap entity.
               if Present (E) then
                  Register_Volatile (E);

                  if Ekind (E) = E_Abstract_State
                    and then Enclosing_Lib_Unit_Entity (E) /= Current_Lib_Unit
                  then
                     pragma Assert (not Local_Vars);
                     Remote_States.Include (Name);
                  end if;
               else
                  pragma Assert (Is_Heap_Variable (Name));
               end if;
            end;
         end loop;
      end Process_Volatiles_And_States;

   --  Start of processing for GG_Register_Global_Info

   begin
      Entity_Infos.Append (GI);

      --  Collect volatile variables and state abstractions; these sets are
      --  disjoint, so it is more efficient to process them separately instead
      --  of doing an expensive union to have a single procedure call.
      if not GI.Local then
         Process_Volatiles_And_States (GI.Globals.Proper.Proof_Ins);
         Process_Volatiles_And_States (GI.Globals.Proper.Inputs);
         Process_Volatiles_And_States (GI.Globals.Proper.Outputs);
         Process_Volatiles_And_States (GI.Local_Variables,
                                       Local_Vars => True);
         Process_Volatiles_And_States (GI.Local_Ghost_Variables,
                                       Local_Vars => True);

         --  In phase 2 we only need to know the initialization status of
         --  proof_ins and inputs; outputs are irrelevant.
         Process_Predefined_Variables (GI.Globals.Proper.Proof_Ins);
         Process_Predefined_Variables (GI.Globals.Proper.Inputs);
      end if;
   end GG_Register_Global_Info;

   ----------------------------------
   -- GG_Register_Max_Queue_Length --
   ----------------------------------

   procedure GG_Register_Max_Queue_Length (EN     : Entity_Name;
                                           Length : Nat)

   is
   begin
      Entries_Max_Queue_Length.Append ((Entry_Name       => EN,
                                        Max_Queue_Length => Length));
   end GG_Register_Max_Queue_Length;

   ----------------------------------
   -- GG_Register_Protected_Object --
   ----------------------------------

   procedure GG_Register_Protected_Object (PO   : Entity_Name;
                                           Prio : Priority_Value)
   is
   begin
      Protected_Instances.Append ((Variable => PO,
                                   Priority => Prio));
   end GG_Register_Protected_Object;

   ----------------------------------
   -- GG_Register_State_Refinement --
   ----------------------------------

   procedure GG_Register_State_Refinement (E : Entity_Id) is
   begin
      for State of Iter (Abstract_States (E)) loop
         --  Append an empty container and then populate it
         State_Constituents.Append
           ((State        => To_Entity_Name (State),
             Constituents => Name_Lists.Empty_List));

         declare
            New_Constituents : Name_Lists.List renames
              State_Constituents (State_Constituents.Last).Constituents;

         begin
            --  ??? how about Part_Of_Constituents?
            for Constituent of Iter (Refinement_Constituents (State)) loop
               if Nkind (Constituent) = N_Null then
                  null;
               else
                  New_Constituents.Append (To_Entity_Name (Constituent));
               end if;
            end loop;
         end;

         --  Check if state is volatile and if it is then add it to the
         --  appropriate sets.
         Register_Volatile (State);
      end loop;
   end GG_Register_State_Refinement;

   -----------------------------
   -- GG_Register_Task_Object --
   -----------------------------

   procedure GG_Register_Task_Object (Type_Name : Entity_Name;
                                      Object    : Task_Object)
   is
   begin
      Task_Instances.Append ((Type_Name => Type_Name,
                              Object    => Object));
   end GG_Register_Task_Object;

   -----------------------
   -- Register_Volatile --
   -----------------------

   procedure Register_Volatile (E : Entity_Id) is
   begin
      --  Only register truly volatile objects, i.e. not constants of a
      --  volatile type (that may only come from code with SPARK_Mode => Off),
      --  because they only act as snapshots of some truly volatile objects.
      if Has_Volatile (E)
        and then Ekind (E) /= E_Constant
      then
         declare
            Name : constant Entity_Name := To_Entity_Name (E);
         begin
            if Has_Volatile_Flavor (E, Pragma_Async_Readers) then
               Async_Readers_Vars.Include (Name);

               if Has_Volatile_Flavor (E, Pragma_Effective_Writes) then
                  Effective_Writes_Vars.Include (Name);
               end if;
            end if;

            if Has_Volatile_Flavor (E, Pragma_Async_Writers) then
               Async_Writers_Vars.Include (Name);

               if Has_Volatile_Flavor (E, Pragma_Effective_Reads) then
                  Effective_Reads_Vars.Include (Name);
               end if;
            end if;
         end;
      end if;
   end Register_Volatile;

   -----------------------
   -- GG_Write_Finalize --
   -----------------------

   procedure GG_Write_Finalize is
      procedure Write_To_ALI (V : in out ALI_Entry);
      --  Helper subprogram to write the given entry to the ALI file

      ------------------
      -- Write_To_ALI --
      ------------------

      procedure Write_To_ALI (V : in out ALI_Entry) is
         A : Archive (Serialisation.Output);
      begin
         Serialize (A, V);
         Write_Info_Str
           ("GG " &
              Ada.Strings.Unbounded.To_String (Serialisation.To_String (A)));
         Write_Info_Terminate;
      end Write_To_ALI;

      V : ALI_Entry;

   --  Start of processing for GG_Write_Finalize

   begin
      --  Write State info
      for SC of State_Constituents loop
         V := (Kind             => EK_State_Map,
               The_State        => SC.State,
               The_Constituents => SC.Constituents);
         Write_To_ALI (V);
      end loop;

      --  Write remote states
      V := (Kind              => EK_Remote_States,
            The_Remote_States => Remote_States);
      Write_To_ALI (V);

      --  Write predefined initialized variables
      V := (Kind                 => EK_Predef_Init_Vars,
            The_Predef_Init_Vars => Predefined_Initialized_Variables);
      Write_To_ALI (V);

      --  Write entity-specific info
      for Info of Entity_Infos loop
         V := (Kind            => EK_Globals,
               The_Global_Info => Info);
         Write_To_ALI (V);
      end loop;

      --  Write Volatile info
      V := (Kind                 => EK_Volatiles,
            The_Async_Readers    => Async_Readers_Vars,
            The_Async_Writers    => Async_Writers_Vars,
            The_Effective_Reads  => Effective_Reads_Vars,
            The_Effective_Writes => Effective_Writes_Vars);
      Write_To_ALI (V);

      --  Write constant calls
      for Constant_Calls of Constant_Calls_List loop
         V := (Kind         => EK_Constant_Calls,
               The_Constant => Constant_Calls.Caller,
               The_Calls    => Constant_Calls.Callees);
         Write_To_ALI (V);
      end loop;

      --  Write direct calls
      for Direct_Calls of Direct_Calls_List loop
         V := (Kind        => EK_Direct_Calls,
               The_Caller  => Direct_Calls.Caller,
               The_Callees => Direct_Calls.Callees);
         Write_To_ALI (V);
      end loop;

      for Entry_List of Entries_Max_Queue_Length loop
         V := (Kind                 => EK_Max_Queue_Length,
               The_Entry            => Entry_List.Entry_Name,
               The_Max_Queue_Length => Entry_List.Max_Queue_Length);
         Write_To_ALI (V);
      end loop;

      for Instance of Task_Instances loop
         V := (Kind        => EK_Task_Instance,
               The_Type    => Instance.Type_Name,
               The_Object  => Instance.Object);
         Write_To_ALI (V);
      end loop;

      for Instance of Protected_Instances loop
         V := (Kind         => EK_Protected_Instance,
               The_Variable => Instance.Variable,
               The_Priority => Instance.Priority);
         Write_To_ALI (V);
      end loop;

      --  Write the finalization string
      V := (Kind => EK_End_Marker);
      Write_To_ALI (V);

      --  Close file and put the package out of writing mode
      Close_Output_Library_Info;
      Current_Mode := GG_No_Mode;
   end GG_Write_Finalize;

   -------------------------
   -- GG_Write_Initialize --
   -------------------------

   procedure GG_Write_Initialize (GNAT_Root : Node_Id) is
   begin
      --  Open output library info for writing
      Open_Output_Library_Info;
      Write_Info_Str ("QQ SPARKVERSION " &
                        SPARK2014_Static_Version_String);
      Write_Info_Terminate;

      --  Set mode to writing mode
      Current_Mode := GG_Write_Mode;

      --  Store the entity of the current compilation unit
      Current_Lib_Unit := Unique_Defining_Entity (Unit (GNAT_Root));
   end GG_Write_Initialize;

end Flow_Generated_Globals.Phase_1;
