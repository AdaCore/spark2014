------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 1        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2014-2016, Altran UK Limited                 --
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

with Einfo;                   use Einfo;
with Lib.Util;                use Lib.Util;
with Osint.C;                 use Osint.C;
with Sem_Util;                use Sem_Util;
with Snames;                  use Snames;

with SPARK_Util;              use SPARK_Util;
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

   Nonblocking_Subprograms : Name_Lists.List;
   --  Subprograms, entries and tasks that do not contain potentially blocking
   --  statements (but still may call another blocking subprogram).

   type Accessed_Tasking_Objects is record
      Caller  : Entity_Name;
      Objects : Tasking_Info;
   end record;

   package Tasking_Info_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Accessed_Tasking_Objects);
   --  Containers with tasking objects accessed by a given caller

   Tasking_Info_List : Tasking_Info_Lists.List;
   --  List with tasking objects directly accessed by subprograms

   Subprogram_Info_List : Global_Info_Lists.List;
   --  Information about subprograms from the "generated globals" algorithm

   Package_Info_List : Global_Info_Lists.List;
   --  Information about packages from the "generated globals" algorithm

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

   Remote_States : Name_Sets.Set;
   --  State abstractions referenced in the current compilation unit but
   --  declared outside of it.

   ----------------------------------------------------------------------
   --  Volatile information
   ----------------------------------------------------------------------

   Async_Writers_Vars    : Name_Sets.Set;
   Async_Readers_Vars    : Name_Sets.Set;
   Effective_Reads_Vars  : Name_Sets.Set;
   Effective_Writes_Vars : Name_Sets.Set;
   --  Volatile information

   procedure Register_Volatile (E : Entity_Id);
   --  Processes F and adds it to Async_Writers_Vars, Async_Readers_Vars,
   --  Effective_Reads_Vars, or Effective_Writes_Vars as appropriate.

   -----------------------------
   -- GG_Register_Global_Info --
   -----------------------------

   procedure GG_Register_Global_Info (GI : Global_Phase_1_Info) is

      procedure Process_Volatiles_And_States (NS : Name_Sets.Set);
      --  Goes through NS, finds volatiles and remote states and stores them in
      --  the appropriate sets.

      -----------------------------------
      -- Processs_Volatiles_And_States --
      -----------------------------------

      procedure Process_Volatiles_And_States (NS : Name_Sets.Set) is
      begin
         for Name of NS loop
            declare
               E : constant Entity_Id := Find_Entity (Name);
            begin
               if Present (E) then
                  Register_Volatile (E);

                  if Ekind (E) = E_Abstract_State
                    and then Enclosing_Comp_Unit_Node (E) /= Current_Comp_Unit
                  then
                     Remote_States.Include (Name);
                  end if;
               end if;
            end;
         end loop;
      end Process_Volatiles_And_States;

   --  Start of processing for GG_Register_Global_Info

   begin
      case GI.Kind is
         when Kind_Entry | Kind_Subprogram | Kind_Task =>
            Subprogram_Info_List.Append (GI);

         when Kind_Package | Kind_Package_Body =>
            Package_Info_List.Append (GI);
      end case;
      --  GG_Exists_Cache.Insert (GI.Name);
      --  ??? not needed in phase 1?

      --  Collect volatile variables and state abstractions; these sets are
      --  disjoints, so it is more efficient to process them separately instead
      --  of doing an expensive union to have a single procedure call.
      Process_Volatiles_And_States (GI.Inputs_Proof);
      Process_Volatiles_And_States (GI.Inputs);
      Process_Volatiles_And_States (GI.Outputs);
      Process_Volatiles_And_States (GI.Local_Variables);
   end GG_Register_Global_Info;

   -----------------------------
   -- GG_Register_Nonblocking --
   -----------------------------

   procedure GG_Register_Nonblocking (EN : Entity_Name) renames
     Nonblocking_Subprograms.Append;

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

   ----------------------------
   -- GG_Register_State_Info --
   ----------------------------

   procedure GG_Register_State_Info (DM : Dependency_Maps.Map) is
   begin
      for S in DM.Iterate loop
         declare
            State_F : Flow_Id renames Dependency_Maps.Key (S);

            State_Entity : constant Entity_Id :=
              Get_Direct_Mapping_Id (State_F);

            State_Name : constant Entity_Name :=
              To_Entity_Name (State_Entity);

         begin
            --  Append new state info into State_Comp_Map
            State_Constituents.Append ((State_Name, Name_Lists.Empty_List));

            declare
               New_Constituents : Name_Lists.List renames
                 State_Constituents (State_Constituents.Last).Constituents;

            begin
               for Constituent of DM (S) loop
                  New_Constituents.Append
                    (To_Entity_Name (Get_Direct_Mapping_Id (Constituent)));
               end loop;
            end;

            --  Check if state is volatile and if it is then add it to the
            --  appropriate sets.
            Register_Volatile (State_Entity);
         end;
      end loop;
   end GG_Register_State_Info;

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

   ------------------------------
   -- GG_Register_Tasking_Info --
   ------------------------------

   procedure GG_Register_Tasking_Info (EN : Entity_Name;
                                       TI : Tasking_Info)
   is
   begin
      Tasking_Info_List.Append ((Caller => EN,
                                 Objects => TI));
   end GG_Register_Tasking_Info;

   -----------------------
   -- Register_Volatile --
   -----------------------

   procedure Register_Volatile (E : Entity_Id) is
      Name : constant Entity_Name := To_Entity_Name (E);
   begin
      if Has_Volatile (E) then

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

      use Common_Containers.Name_Graphs;

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
      V := (Kind          => EK_Remote_States,
            Remote_States => Remote_States);
      Write_To_ALI (V);

      --  Write globals for package and subprograms/tasks
      for Info of Package_Info_List loop
         V := (Kind            => EK_Globals,
               The_Global_Info => Info);
         Write_To_ALI (V);
      end loop;

      for Info of Subprogram_Info_List loop
         V := (Kind            => EK_Globals,
               The_Global_Info => Info);
         Write_To_ALI (V);
      end loop;

      --  Write Volatile info
      V := (Kind                 => EK_Volatiles,
            Async_Readers    => Async_Readers_Vars,
            Async_Writers    => Async_Writers_Vars,
            Effective_Reads  => Effective_Reads_Vars,
            Effective_Writes => Effective_Writes_Vars);
      Write_To_ALI (V);

      --  Write nonblocking subprograms
      V := (Kind                        => EK_Nonblocking,
            The_Nonblocking_Subprograms => Nonblocking_Subprograms);
      Write_To_ALI (V);

      for Subprogram of Tasking_Info_List loop
         V := (Kind             => EK_Tasking_Info,
               The_Entity       => Subprogram.Caller,
               The_Tasking_Info => <>);

         for Kind in Tasking_Info_Kind loop
            V.The_Tasking_Info (Kind) :=
              To_Name_Set (Subprogram.Objects (Kind));
         end loop;

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

      --  Store the current compilation unit on which we are working
      Current_Comp_Unit := GNAT_Root;
   end GG_Write_Initialize;

end Flow_Generated_Globals.Phase_1;
