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

with Flow_Generated_Globals.ALI_Serialization;
use Flow_Generated_Globals.ALI_Serialization;

with Atree;                   use Atree;
with Ada.Strings.Unbounded;
with Lib.Util;                use Lib.Util;
with Osint.C;                 use Osint.C;
with Serialisation;           use Serialisation;
with SPARK_Frame_Conditions;  use SPARK_Frame_Conditions;

package body Flow_Generated_Globals.Phase_1 is

   package Entity_Name_To_Priority_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Element_Type => Object_Priority);
   --  List of variables containing protected objects and their static
   --  priorities; for priority ceiling checks.

   Protected_Objects : Entity_Name_To_Priority_Lists.List;
   --  Mapping from variables containing protected objects to their static
   --  priorities; for priority ceiling checks.
   --
   --  In phase 1 it is populated with information from current compilation
   --  unit. In phase 2 this information is collected for all variables
   --  accessible from the current compilation unit (including variables
   --  declared in bodies of other packages).

   Nonblocking_Subprograms : Name_Sets.Set := Name_Sets.Empty_Set;
   --  Subprograms, entries and tasks that do not contain potentially blocking
   --  statements (but still may call another blocking subprogram).

   Tasking_Info_Bag : array (Tasking_Info_Kind) of Name_Graphs.Map :=
     (others => Name_Graphs.Empty_Map);
   --  Maps from subprogram names to accessed objects
   --
   --  In phase 1 it is populated with objects directly accessed by each
   --  subprogram and stored in the ALI file. In phase 2 it is populated
   --  with objects directly and indirectly accessed by each subprogram.

   Subprogram_Info_List        : Global_Info_Lists.List :=
     Global_Info_Lists.Empty_List;
   --  Information about subprograms from the "generated globals" algorithm

   Package_Info_List           : Global_Info_Lists.List :=
     Global_Info_Lists.Empty_List;
   --  Information about packages from the "generated globals" algorithm

   -----------------------------
   -- GG_Register_Nonblocking --
   -----------------------------

   procedure GG_Register_Nonblocking (EN : Entity_Name) is
   begin
      Nonblocking_Subprograms.Insert (EN);
   end GG_Register_Nonblocking;

   ----------------------------------
   -- GG_Register_Protected_Object --
   ----------------------------------

   procedure GG_Register_Protected_Object (PO   : Entity_Name;
                                           Prio : Priority_Value)
   is
   begin
      Protected_Objects.Append (Object_Priority'(Variable => PO,
                                                 Priority => Prio));
   end GG_Register_Protected_Object;

   ------------------------------
   -- GG_Register_Tasking_Info --
   ------------------------------

   procedure GG_Register_Tasking_Info (EN : Entity_Name;
                                       TI : Tasking_Info)
   is
   begin
      for Kind in Tasking_Info_Kind loop
         Tasking_Info_Bag (Kind).Insert (EN, To_Name_Set (TI (Kind)));
      end loop;
   end GG_Register_Tasking_Info;

   -----------------------
   -- GG_Write_Finalize --
   -----------------------

   procedure GG_Write_Finalize is
      procedure Write_To_ALI (V : in out ALI_Entry);
      --  Helper subprogram to write the given entry to the ALI file.
      --  Second parameter has to be in out because of the way serialize
      --  works.

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
      for C in State_Comp_Map.Iterate loop
         V := (Kind             => EK_State_Map,
               The_State        => Key (C),
               The_Constituents => State_Comp_Map (C));
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
            All_Async_Readers    => Async_Readers_Vars,
            All_Async_Writers    => Async_Writers_Vars,
            All_Effective_Reads  => Effective_Reads_Vars,
            All_Effective_Writes => Effective_Writes_Vars);
      Write_To_ALI (V);

      --  Write nonblocking subprograms
      V := (Kind                        => EK_Tasking_Nonblocking,
            The_Nonblocking_Subprograms => Nonblocking_Subprograms);
      Write_To_ALI (V);

      --  Write tasking-related information. This is a bit awkward since we
      --  need to rotate the information in Tasking_Info_Bag.
      declare
         All_Names : Name_Sets.Set := Name_Sets.Empty_Set;
      begin
         for Kind in Tasking_Info_Kind loop
            for C in Tasking_Info_Bag (Kind).Iterate loop
               All_Names.Include (Key (C));
            end loop;
         end loop;
         for Name of All_Names loop
            V := (Kind             => EK_Tasking_Info,
                  The_Entity       => Name,
                  The_Tasking_Info => <>);
            for Kind in Tasking_Info_Kind loop
               declare
                  Phase_1_Info : Name_Graphs.Map renames
                    Tasking_Info_Bag (Kind);

                  C : constant Name_Graphs.Cursor := Phase_1_Info.Find (Name);

               begin
                  V.The_Tasking_Info (Kind) := (if Has_Element (C)
                                                then Phase_1_Info (C)
                                                else Name_Sets.Empty_Set);
               end;
            end loop;
            Write_To_ALI (V);
         end loop;
      end;

      for C in Task_Instances.Iterate loop
         V := (Kind        => EK_Tasking_Instance_Count,
               The_Type    => Task_Instances_Maps.Key (C),
               The_Objects => Task_Instances (C));
         Write_To_ALI (V);
      end loop;

      for PO of Protected_Objects loop
         V := (Kind         => EK_Protected_Variable,
               The_Variable => PO.Variable,
               The_Priority => PO.Priority);
         Write_To_ALI (V);
      end loop;

      --  Write the finalization string.
      V := (Kind => EK_End_Marker);
      Write_To_ALI (V);

      --  Close file and put the package out of writing mode.
      Close_Output_Library_Info;
      Current_Mode := GG_No_Mode;
   end GG_Write_Finalize;

   --------------------------
   -- GG_Write_Global_Info --
   --------------------------

   procedure GG_Write_Global_Info (GI : Global_Phase_1_Info) is
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
                  Add_To_Volatile_Sets_If_Volatile (Direct_Mapping_Id (E));
                  Add_To_Remote_States (Direct_Mapping_Id (E));
               end if;
            end;
         end loop;
      end Process_Volatiles_And_States;

   --  Start of processing for GG_Write_Global_Info

   begin
      case GI.Kind is
         when Kind_Entry | Kind_Subprogram | Kind_Task =>
            Subprogram_Info_List.Append (GI);

         when Kind_Package | Kind_Package_Body =>
            Package_Info_List.Append (GI);
      end case;
      --  GG_Exists_Cache.Insert (GI.Name);
      --  ??? not needed in phase 1?

      --  Gather and save volatile variables and state abstractions
      Process_Volatiles_And_States (GI.Inputs_Proof);
      Process_Volatiles_And_States (GI.Inputs);
      Process_Volatiles_And_States (GI.Outputs);
      Process_Volatiles_And_States (GI.Local_Variables);
   end GG_Write_Global_Info;

   -------------------------
   -- GG_Write_Initialize --
   -------------------------

   procedure GG_Write_Initialize (GNAT_Root : Node_Id) is
   begin
      --  Open output library info for writing
      Open_Output_Library_Info;

      --  Set mode to writing mode
      Current_Mode := GG_Write_Mode;

      --  Store the current compilation unit on which we are working
      Current_Comp_Unit := GNAT_Root;
   end GG_Write_Initialize;

   -------------------------
   -- GG_Write_State_Info --
   -------------------------

   procedure GG_Write_State_Info (DM : Dependency_Maps.Map) is
   begin
      for S in DM.Iterate loop
         declare
            State_F      : Flow_Id renames Dependency_Maps.Key (S);

            State_N      : constant Entity_Name :=
              To_Entity_Name (Get_Direct_Mapping_Id (State_F));

            Constituents : constant Name_Sets.Set :=
              To_Name_Set (To_Node_Set (DM (S)));
         begin
            --  Include (possibly overwrite) new state info into State_Comp_Map
            State_Comp_Map.Include (State_N, Constituents);

            --  Check if State_F is volatile and if it is then add it to the
            --  appropriate sets.
            Add_To_Volatile_Sets_If_Volatile (State_F);
         end;
      end loop;
   end GG_Write_State_Info;

end Flow_Generated_Globals.Phase_1;
