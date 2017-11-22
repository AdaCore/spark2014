------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 1        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2014-2018, Altran UK Limited                 --
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
with Flow_Generated_Globals.Phase_1.Write;
use Flow_Generated_Globals.Phase_1.Write;
with Serialisation;           use Serialisation;

package body Flow_Generated_Globals.Phase_1 is

   package Partial_Contract_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Partial_Contract);

   Entity_Infos : Partial_Contract_Lists.List;
   --  Entity-specific information as discovered by their analysis
   --
   --  ??? we keep this locally only because in the ALI file we first want to
   --  have entity-independent info; perhaps we do not care and can safely
   --  dump information locally for each scope.

   Current_Lib_Unit : Entity_Id;
   --  Unique identifier of the top-level entity of the current library unit;
   --  it is the same for the main compilation unit and its subunits (which are
   --  processed in the same invocation of gnat2why).

   Remote_States : Node_Sets.Set;
   --  State abstractions referenced in the current compilation unit but
   --  declared outside of it.

   Predefined_Initialized_Variables : Node_Sets.Set;
   --  Variables in predefined units that are known to be initialized. We
   --  attach them to units where they are used as inputs or proof_ins, because
   --  in phase 2 we might only know them by Entity_Name (which is not enough
   --  to decide their initialization status).

   Ghost_Entities : Node_Sets.Set;
   --  Entities marked with a Ghost aspect

   CAE_Entities : Node_Sets.Set;
   --  Entities marked with a Constant_After_Elaboration aspect

   ----------------------------------------------------------------------
   --  Volatile information
   ----------------------------------------------------------------------

   Async_Writers_Vars    : Node_Sets.Set;
   Async_Readers_Vars    : Node_Sets.Set;
   Effective_Reads_Vars  : Node_Sets.Set;
   Effective_Writes_Vars : Node_Sets.Set;
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
      New_GG_Line (EK_Constant_Calls);
      Serialize (E);
      Serialize (Calls);
      Terminate_GG_Line;
   end GG_Register_Constant_Calls;

   ------------------------------
   -- GG_Register_Direct_Calls --
   ------------------------------

   procedure GG_Register_Direct_Calls (E : Entity_Id; Calls : Node_Sets.Set) is
   begin
      New_GG_Line (EK_Direct_Calls);
      Serialize (E);
      Serialize (Calls);
      Terminate_GG_Line;

      --  Sanity check (this seems to be the most a convenient place for it):
      --
      --  Generic actual subprograms should not appear in direct calls, except
      --  for default subprograms. They are either null procedures or functions
      --  that wrap arbitrary expressions.

      for Call of Calls loop
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
      end loop;
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

      procedure Process_Ghost (Names : Name_Sets.Set);
      --  Goes through Names, finds ghost objects and stores them in the
      --  appropriate container.

      procedure Process_CAE (Names : Name_Sets.Set);
      --  Goes through Names, finds Costant_After_Elaboration variables and
      --  stores them in the appropriate container.

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
                  Predefined_Initialized_Variables.Include (E);
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
                     Remote_States.Include (E);
                  end if;
               else
                  pragma Assert (Is_Heap_Variable (Name));
               end if;
            end;
         end loop;
      end Process_Volatiles_And_States;

      -------------------
      -- Process_Ghost --
      -------------------

      procedure Process_Ghost (Names : Name_Sets.Set) is
      begin
         for Name of Names loop
            declare
               E : constant Entity_Id := Find_Entity (Name);

            begin
               --  Convert name back to Entity_Id; this should work for
               --  everything except the special __HEAP name that represent a
               --  non-existing heap entity.
               if Present (E)
                 and then Is_Ghost_Entity (E)
               then
                  Ghost_Entities.Include (E);
               end if;
            end;
         end loop;
      end Process_Ghost;

      -----------------
      -- Process_CAE --
      -----------------

      procedure Process_CAE (Names : Name_Sets.Set) is
      begin
         for Name of Names loop
            declare
               E : constant Entity_Id := Find_Entity (Name);

            begin
               --  Convert name back to Entity_Id; this should work for
               --  everything except the special __HEAP name that represent a
               --  non-existing heap entity.
               if Present (E)
                 and then Ekind (E) = E_Variable
                 and then Is_Constant_After_Elaboration (E)
               then
                  CAE_Entities.Include (E);
               end if;
            end;
         end loop;
      end Process_CAE;

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
         Process_Volatiles_And_States (GI.Local_Variables, Local_Vars => True);

         --  Collect ghost entities
         Process_Ghost (GI.Globals.Proper.Proof_Ins);
         Process_Ghost (GI.Globals.Proper.Inputs);
         Process_Ghost (GI.Globals.Proper.Outputs);

         --  Collect CAE Entities
         Process_CAE (GI.Globals.Proper.Proof_Ins);
         Process_CAE (GI.Globals.Proper.Inputs);
         Process_CAE (GI.Globals.Proper.Outputs);

         --  In phase 2 we only need to know the initialization status of
         --  proof_ins and inputs; outputs are irrelevant.
         Process_Predefined_Variables (GI.Globals.Proper.Proof_Ins);
         Process_Predefined_Variables (GI.Globals.Proper.Inputs);
      end if;
   end GG_Register_Global_Info;

   ----------------------------------
   -- GG_Register_Max_Queue_Length --
   ----------------------------------

   procedure GG_Register_Max_Queue_Length (E : String; Length : Nat) is
   begin
      New_GG_Line (EK_Max_Queue_Length);
      Serialize (E);
      Serialize (Length);
      Terminate_GG_Line;
   end GG_Register_Max_Queue_Length;

   ----------------------------------
   -- GG_Register_Protected_Object --
   ----------------------------------

   procedure GG_Register_Protected_Object (PO   : Entity_Id;
                                           Prio : Priority_Value)
   is
      procedure Serialize is new
        Flow_Generated_Globals.Phase_1.Write.Serialize_Discrete
          (Priority_Kind);
   begin
      New_GG_Line (EK_Protected_Instance);
      Serialize (PO);
      Serialize (Prio.Kind);
      if Prio.Kind = Static then
         Serialize (Prio.Value);
      end if;
      Terminate_GG_Line;
   end GG_Register_Protected_Object;

   ----------------------------------
   -- GG_Register_State_Refinement --
   ----------------------------------

   procedure GG_Register_State_Refinement (E : Entity_Id) is
   begin
      for State of Iter (Abstract_States (E)) loop
         New_GG_Line (EK_State_Map);
         Serialize (State);

         if Has_Null_Refinement (State) then
            Serialize (No_Elist);
         else
            Serialize (Refinement_Constituents (State));
         end if;

         Terminate_GG_Line;

         --  Check if state is volatile and if it is then add it to the
         --  appropriate sets.
         Register_Volatile (State);
      end loop;
   end GG_Register_State_Refinement;

   -----------------------------
   -- GG_Register_Task_Object --
   -----------------------------

   procedure GG_Register_Task_Object (Typ       : Entity_Id;
                                      Object    : Entity_Id;
                                      Instances : Instance_Number)
   is
   begin
      New_GG_Line (EK_Task_Instance);
      Serialize (Typ);
      Serialize (Object);
      Serialize (Instances);
      Terminate_GG_Line;
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
         if Has_Volatile_Flavor (E, Pragma_Async_Readers) then
            Async_Readers_Vars.Include (E);

            if Has_Volatile_Flavor (E, Pragma_Effective_Writes) then
               Effective_Writes_Vars.Include (E);
            end if;
         end if;

         if Has_Volatile_Flavor (E, Pragma_Async_Writers) then
            Async_Writers_Vars.Include (E);

            if Has_Volatile_Flavor (E, Pragma_Effective_Reads) then
               Effective_Reads_Vars.Include (E);
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

   --  Start of processing for GG_Write_Finalize

   begin
      --  Write entity-specific info
      for Info of Entity_Infos loop
         V := (Kind            => EK_Globals,
               The_Global_Info => Info);
         Write_To_ALI (V);
      end loop;

      --  The remaining entries are not specific to individual entities; it is
      --  the minimum information for objects (possibly from other compilation
      --  for which we will not have an ALI file at all, e.g. predefined units)
      --  that is needed in phase 2.

      if not Remote_States.Is_Empty then
         New_GG_Line (EK_Remote_States);
         Serialize (Remote_States);
         Terminate_GG_Line;
      end if;

      if not Predefined_Initialized_Variables.Is_Empty then
         New_GG_Line (EK_Predef_Init_Vars);
         Serialize (Predefined_Initialized_Variables);
         Terminate_GG_Line;
      end if;

      if not Async_Readers_Vars.Is_Empty
        or else not Async_Writers_Vars.Is_Empty
        or else not Effective_Reads_Vars.Is_Empty
        or else not Effective_Writes_Vars.Is_Empty
      then
         New_GG_Line (EK_Volatiles);
         Serialize (Async_Readers_Vars,    "AR");
         Serialize (Async_Writers_Vars,    "AW");
         Serialize (Effective_Reads_Vars,  "ER");
         Serialize (Effective_Writes_Vars, "EW");
         Terminate_GG_Line;
      end if;

      if not Ghost_Entities.Is_Empty then
         New_GG_Line (EK_Ghost_Entities);
         Serialize (Ghost_Entities);
         Terminate_GG_Line;
      end if;

      if not CAE_Entities.Is_Empty then
         New_GG_Line (EK_CAE_Entities);
         Serialize (CAE_Entities);
         Terminate_GG_Line;
      end if;

      --  Write the finalization string
      New_GG_Line (EK_End_Marker);
      Terminate_GG_Line;

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
      Write_Info_Str ("QQ SPARKVERSION " & SPARK2014_Static_Version_String);
      Write_Info_Terminate;

      --  Set mode to writing mode
      Current_Mode := GG_Write_Mode;

      --  Store the entity of the current compilation unit
      Current_Lib_Unit := Unique_Defining_Entity (Unit (GNAT_Root));
   end GG_Write_Initialize;

end Flow_Generated_Globals.Phase_1;
