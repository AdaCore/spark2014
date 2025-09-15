------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 1        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2014-2025, Capgemini Engineering              --
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

with Aspects;     use Aspects;
with Einfo.Utils; use Einfo.Utils;
with Elists;      use Elists;
with Lib.Util;    use Lib.Util;
with Namet;       use Namet;
with Osint.C;     use Osint.C;
with Sem_Aux;     use Sem_Aux;
with Sem_Eval;    use Sem_Eval;
with Sem_Util;    use Sem_Util;
with Sinfo.Utils; use Sinfo.Utils;
with Snames;      use Snames;
with Uintp;       use Uintp;

with Common_Iterators;       use Common_Iterators;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with SPARK2014VSN;           use SPARK2014VSN;

with Flow_Generated_Globals.Phase_1.Write;
use Flow_Generated_Globals.Phase_1.Write;

with Flow_Generated_Globals.Traversal; use Flow_Generated_Globals.Traversal;

package body Flow_Generated_Globals.Phase_1 is

   Current_Lib_Unit : Entity_Id;
   --  Unique identifier of the top-level entity of the current library unit;
   --  it is the same for the main compilation unit and its subunits (which are
   --  processed in the same invocation of gnat2why).

   Remote_States : Node_Sets.Set;
   --  State abstractions referenced in the current compilation unit but
   --  declared outside of it.

   Predefined_Initialized_Entities : Node_Sets.Set;
   --  Variables and abstract states in predefined units that are known to be
   --  initialized. We attach them to units where they are used as inputs or
   --  proof_ins, because in phase 2 we might only know them by Entity_Name
   --  (which is not enough to decide their initialization status).

   Constants : Node_Sets.Set;
   --  Constants

   Checked_Ghost_Entities : Node_Sets.Set;
   --  Entities marked as Ghost, but with policy Checked

   Ignored_Ghost_Entities : Node_Sets.Set;
   --  Entities marked as Ghost, but with policy Ignore

   CAE_Entities : Node_Sets.Set;
   --  Entities marked with a Constant_After_Elaboration aspect

   Protected_Objects : Node_Sets.Set;
   --  Protected objects or records/array objects that have a protected type
   --  as a field/component.

   Protected_Operations : Node_Sets.Set;
   --  Referenced protected operations

   ----------------------------------------------------------------------
   --  Protected types information
   ----------------------------------------------------------------------

   procedure GG_Register_Max_Queue_Length (E : String; Length : Nat);
   --  Register the value of Max_Queue_Length for an entry (which is
   --  represented as a string that uniquely identifies different entries
   --  belonging to the same an object, i.e. (in the regexp syntax)
   --  "(package__)+object(__component)*__entry".

   procedure GG_Register_Protected_Object
     (PO : Entity_Id; PT : Entity_Id; Prio : Priority_Value)
   with Pre => Ekind (PO) = E_Variable and then Ekind (PT) = E_Protected_Type;
   --  Register protected object or an object with protected components.
   --
   --  The following data are recorded:
   --  * Type - The type of the object or its protected component.
   --  * Object - A protected object or object with protected components.
   --  * Priority kind.
   --  * Piority value (only if kind = Static).
   --
   --  Note that in SPARK the priority is always determined by a type. Hence,
   --  there will be some redundancy as different objects of the same type will
   --  record the same priority value. We could instead store a type, priority
   --  and all the objects in one entry. However, this is not important since
   --  the type-priority mapping is normalized and its consistency is checked
   --  in Phase 2 where we aggregate data from multiple units.
   --
   --  @param PO   - The object to serialize
   --  @param PT   - The type of PO
   --  @param Prio - Priority of PO or the serialized component

   procedure Register_PO_Info (PO : Entity_Id; PT : Entity_Id; Prefix : String)
   with
     Pre =>
       Ekind (PO) = E_Variable
       and then Is_Type (PT)
       and then Prefix'Length > 0;
   --  Register the protected object, its type and priorty, and if the object
   --  has entries then also their Max_Queue_Length.

   procedure GG_Register_Protected_Operation (Op : Entity_Id)
   with Pre => Ekind (Op) in E_Procedure | E_Function | E_Entry;
   --  Register a protected operation and the type where it belongs.
   --
   --  The following data are recorded:
   --  * Op - The protected operation.
   --  * Typ - The protected type where Op belongs.
   --
   --  Note: There is some redundancy because the same information is also
   --  recorded in EK_Globals provided that a globals entry for Op is created
   --  in the ALI. However, the globals entry is not created for operations
   --  from predefined types like those in GNAT.Semaphores. For the latter use
   --  case we still need to record this mapping.

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

   Synchronized_Vars : Node_Sets.Set;
   --  Synchronized variables acting as globals
   --
   --  We separate this from the unsynchronized objects that we store to check
   --  conflicting accesses between multiple tasks, so that we can detect
   --  accesses from handlers regardless if they are coordinated via protected
   --  subprograms.

   procedure Register_Synchronized (E : Entity_Id);
   --  Register E as a synchronized global object

   --------------------------------
   -- GG_Register_Constant_Calls --
   --------------------------------

   procedure GG_Register_Constant_Calls
     (E : Entity_Id; Calls : Node_Lists.List) is
   begin
      New_GG_Line (EK_Constant_Calls);
      Serialize (E);
      Serialize (Calls);
      Terminate_GG_Line;
   end GG_Register_Constant_Calls;

   ------------------------------
   -- GG_Register_Direct_Calls --
   ------------------------------

   procedure GG_Register_Calls
     (E : Entity_Id; Calls : Node_Sets.Set; Kind : ALI_Entry_Kind) is
   begin
      New_GG_Line (Kind);
      Serialize (E);
      Serialize (Calls);
      Terminate_GG_Line;

      --  Sanity check (this seems to be the most a convenient place for it):
      --
      --  Generic actual subprograms should not appear in direct calls, except
      --  for default subprograms. If they are procedures, then they either are
      --  null procedures, have aspects coming from contracts on generic formal
      --  subprograms or are wrappers for subprogram renamings that involve
      --  access-to-subprogram; if they are functions, then they wrap arbitrary
      --  expressions.

      for Call of Calls loop
         pragma
           Assert
             (if Is_Subprogram (Call)
                  and then Is_Generic_Actual_Subprogram (Call)
                then
                  (case Ekind (Call) is
                     when E_Procedure =>
                       Null_Present (Subprogram_Specification (Call))
                       or else Has_Aspects (Subprogram_Spec (Call))
                       or else Nkind (Original_Node (Subprogram_Spec (Call)))
                               = N_Subprogram_Renaming_Declaration,
                     when E_Function  => True,
                     when others      => raise Program_Error));
      end loop;
   end GG_Register_Calls;

   -------------------------------
   -- GG_Register_Locking_Calls --
   -------------------------------

   procedure GG_Register_Locking_Calls
     (E : Entity_Id; Calls : Tasking_Info_Ext) is
   begin
      for Call in Calls.Iterate loop
         declare
            Prot_Obj  : Entity_Id renames
              Locking_Target_Maps.Key (Call).Object;
            Prot_Typ  : Entity_Id renames Locking_Target_Maps.Key (Call).Typ;
            Called_Op : Entity_Id renames Calls (Call);
         begin
            New_GG_Line (EK_Locking_Call);
            Serialize (E);
            Serialize (Prot_Obj);
            Serialize (Prot_Typ);
            Serialize (Called_Op);
            Terminate_GG_Line;
         end;
      end loop;
   end GG_Register_Locking_Calls;

   -----------------------------
   -- GG_Register_Global_Info --
   -----------------------------

   procedure GG_Register_Global_Info
     (E                 : Entity_Id;
      Local             : Boolean;
      Is_Protected      : Boolean;
      Is_Library_Level  : Boolean;
      Origin            : Globals_Origin_T;

      Globals           : Flow_Nodes;

      Local_Packages    : Node_Sets.Set;
      Local_Variables   : Node_Sets.Set;

      Entries_Called    : Entry_Call_Sets.Set;
      Tasking           : Tasking_Info;
      Tasking_Ext       : Tasking_Info_Ext;

      Always_Terminates : Boolean;
      Has_Subp_Variant  : Boolean;
      No_Body           : Boolean;
      Nonreturning      : Boolean;
      Nonblocking       : Boolean;
      Calls_Via_Access  : Boolean)
   is
      procedure Process_Volatiles_And_States
        (Objects : Node_Sets.Set; Local_Vars : Boolean := False);
      --  Goes through Objects, finds volatiles and remote states and stores
      --  them in the appropriate containers. Local_Vars should be set to true
      --  when processing local variables for a run-time check that they do not
      --  represent remote states.

      procedure Process_Predefined_Entities (Objects : Node_Sets.Set);
      --  Similarly to registering so called "remote states", i.e. states that
      --  are pulled from other compilation units and might only be known by
      --  Entity_Name in phase 2, we need to register variables and abstract
      --  states in predefined units to know their initialization status.

      procedure Process_Ghost (Objects : Node_Sets.Set);
      --  Picks ghost entities from Objects and stores them in the appropriate
      --  container.

      procedure Process_Constants (Objects : Node_Sets.Set);
      --  Picks constants from Objects and stores them in the appropriate
      --  container.

      procedure Process_CAE (Objects : Node_Sets.Set);
      --  Goes through Objects, finds Constant_After_Elaboration variables and
      --  stores them in the appropriate container.

      procedure Process_Protected_Objects (Tasking_Ext : Tasking_Info_Ext);
      --  Stores protected objects that E locks and the protected operations it
      --  calls in appropriate containers.

      procedure Serialize is new Serialize_Discrete (Boolean);
      procedure Serialize is new Serialize_Discrete (Entity_Kind);
      procedure Serialize is new Serialize_Discrete (Globals_Origin_T);

      procedure Serialize (G : Global_Nodes; Label : String);
      procedure Serialize (Entries_Called : Entry_Call_Sets.Set);
      procedure Serialize (Info : Tasking_Info);

      ---------------
      -- Serialize --
      ---------------

      procedure Serialize (G : Global_Nodes; Label : String) is
      begin
         Serialize (G.Proof_Ins, Label & "proof_in");
         Serialize (G.Inputs, Label & "input");
         Serialize (G.Outputs, Label & "output");
      end Serialize;

      procedure Serialize (Entries_Called : Entry_Call_Sets.Set) is
      begin
         Serialize (Tasking_Info_Kind'Image (Entry_Calls));

         Serialize (Int (Entries_Called.Length));

         for EC of Entries_Called loop
            --  For entry calls pretend that we are accessing an object
            --  Package_Name.Object_Name.Entry_Name.
            Serialize
              (Full_Entry_Name (EC.Prefix)
               & "__"
               & Get_Name_String (Chars (EC.Entr)));
         end loop;
      end Serialize;

      procedure Serialize (Info : Tasking_Info) is
      begin
         for Kind in Tasking_Info'Range loop
            Serialize (Info (Kind), Kind'Img);
         end loop;
      end Serialize;

      ---------------------------------
      -- Process_Predefined_Entities --
      ---------------------------------

      procedure Process_Predefined_Entities (Objects : Node_Sets.Set) is
      begin
         for E of Objects loop
            if not Is_Heap_Variable (E)
              and then Is_Predefined_Initialized_Entity (E)
            then
               Predefined_Initialized_Entities.Include (E);
            end if;
         end loop;
      end Process_Predefined_Entities;

      ----------------------------------
      -- Process_Volatiles_And_States --
      ----------------------------------

      procedure Process_Volatiles_And_States
        (Objects : Node_Sets.Set; Local_Vars : Boolean := False) is
      begin
         for E of Objects loop
            if not Is_Heap_Variable (E) then
               Register_Volatile (E);

               Register_Synchronized (E);

               if Ekind (E) = E_Abstract_State
                 and then Enclosing_Lib_Unit_Entity (E) /= Current_Lib_Unit
               then
                  pragma Assert (not Local_Vars);
                  Remote_States.Include (E);
               end if;
            end if;
         end loop;
      end Process_Volatiles_And_States;

      -------------------
      -- Process_Ghost --
      -------------------

      procedure Process_Ghost (Objects : Node_Sets.Set) is
      begin
         for E of Objects loop
            if Is_Checked_Ghost_Entity (E) then
               Checked_Ghost_Entities.Include (E);
            elsif Is_Ignored_Ghost_Entity (E) then
               Ignored_Ghost_Entities.Include (E);
            end if;
         end loop;
      end Process_Ghost;

      -----------------------
      -- Process_Constants --
      -----------------------

      procedure Process_Constants (Objects : Node_Sets.Set) is
      begin
         for E of Objects loop
            if Ekind (E) = E_Constant then
               Constants.Include (E);
            end if;
         end loop;
      end Process_Constants;

      -----------------
      -- Process_CAE --
      -----------------

      procedure Process_CAE (Objects : Node_Sets.Set) is
      begin
         for E of Objects loop
            if Ekind (E) = E_Variable
              and then Is_Constant_After_Elaboration (E)
            then
               CAE_Entities.Include (E);
            end if;
         end loop;
      end Process_CAE;

      -------------------------------
      -- Process_Protected_Objects --
      -------------------------------

      procedure Process_Protected_Objects (Tasking_Ext : Tasking_Info_Ext) is
      begin
         for Position in Tasking_Ext.Iterate loop
            declare
               Object         : Entity_Id renames
                 Locking_Target_Maps.Key (Position).Object;
               Protected_Call : Entity_Id renames Tasking_Ext (Position);
            begin
               --  Register the locked protected object
               Protected_Objects.Include (Object);

               --  Also register the called protected operation from that
               --  object. This is to be able to later record the
               --  operation-type mapping for each protected operation that may
               --  be either a source or target of a call chain that must be
               --  checked. Note that the operation might not necessarily be
               --  defined in the current unit (e.g., its parent is defined in
               --  a system package) and thus there might not exist an
               --  EK_Globals entry for this operation.
               Protected_Operations.Include (Protected_Call);
            end;
         end loop;
      end Process_Protected_Objects;

      --  Start of processing for GG_Register_Global_Info

   begin
      New_GG_Line (EK_Globals);

      Serialize (E);
      Serialize (Local, "local");
      Serialize (Ekind (E));
      if Ekind (E) in E_Function | E_Procedure then
         Serialize (Is_Protected);
      end if;
      if Ekind (E) = E_Package then
         Serialize (Is_Library_Level);
      end if;
      Serialize (Origin);
      Serialize (Traversal_Parents (E));
      Serialize (Globals.Proper, "proper_");  -- ??? replace _ with :
      Serialize (Globals.Refined, "refined_");
      if Ekind (E) = E_Package then
         Serialize (Globals.Initializes.Proper, "initializes");
         --  Normally we don't write an "Initializes" contract for refined
         --  state, however this information is required by phase 2.
         Serialize (Globals.Initializes.Refined, "refined_initializes");
      end if;
      Serialize (Globals.Calls.Proof_Calls, "calls_proof");
      Serialize (Globals.Calls.Definite_Calls, "calls");
      Serialize (Globals.Calls.Conditional_Calls, "calls_conditional");

      if Ekind (E) = E_Package then
         Serialize (Local_Packages, "local_packages");
         Serialize (Local_Variables, "local_var");
      end if;

      if Ekind (E)
         in Entry_Kind | E_Function | E_Procedure | E_Task_Type | E_Package
      then
         --  ??? use Is_Proper_Callee here
         if Ekind (E) /= E_Task_Type then
            Serialize (Always_Terminates);
            Serialize (Has_Subp_Variant);
            Serialize (No_Body);
            Serialize (Nonreturning);
            Serialize (Nonblocking);
            Serialize (Calls_Via_Access);
         end if;

         Serialize (Entries_Called);
         Serialize (Tasking);
      end if;

      Terminate_GG_Line;

      --  Collect referenced protected objects

      Process_Protected_Objects (Tasking_Ext);

      if not Local then
         --  If the current entity is non-local, i.e. can be called from
         --  other compilation units, then it must be library-level (or is
         --  a protected operation/task entry of a library-level concurrent
         --  object). Consequently, all of their global objects must be
         --  library-level as well.

         pragma
           Assert
             (Is_Library_Level_Entity (E)
                or else (Is_Concurrent_Type (Scope (E))
                         and then Is_Library_Level_Entity (Scope (E))));

         --  Collect volatile variables and state abstractions; these sets are
         --  disjoint, so it is more efficient to process them separately
         --  instead of doing an expensive union to have a single procedure
         --  call.

         Process_Volatiles_And_States (Globals.Refined.Proof_Ins);
         Process_Volatiles_And_States (Globals.Refined.Inputs);
         Process_Volatiles_And_States (Globals.Refined.Outputs);

         Process_Volatiles_And_States (Globals.Proper.Proof_Ins);
         Process_Volatiles_And_States (Globals.Proper.Inputs);
         Process_Volatiles_And_States (Globals.Proper.Outputs);
         Process_Volatiles_And_States (Local_Variables, Local_Vars => True);

         --  Collect ghost entities

         Process_Ghost (Globals.Proper.Proof_Ins);
         Process_Ghost (Globals.Proper.Inputs);
         Process_Ghost (Globals.Proper.Outputs);

         --  Collect constants

         Process_Constants (Globals.Proper.Proof_Ins);
         Process_Constants (Globals.Proper.Inputs);

         --  Collect CAE Entities

         Process_CAE (Globals.Proper.Proof_Ins);
         Process_CAE (Globals.Proper.Inputs);
         Process_CAE (Globals.Proper.Outputs);

         --  In phase 2 we only need to know the initialization status of
         --  proof_ins and inputs; outputs are irrelevant.

         Process_Predefined_Entities (Globals.Proper.Proof_Ins);
         Process_Predefined_Entities (Globals.Proper.Inputs);
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

   -----------------------------
   -- Protected_Type_Priority --
   -----------------------------

   function Protected_Type_Priority (Typ : Entity_Id) return Priority_Value is
      Dummy : constant Int := 0;
      --  Dummy priority value, only used to ensure full initialization

      Priority_Expr : constant Node_Id :=
        Get_Priority_Or_Interrupt_Priority (Typ);
   begin
      if Present (Priority_Expr) then
         if Is_OK_Static_Expression (Priority_Expr) then
            return
              Priority_Value'
                (Kind  => Static,
                 Value => UI_To_Int (Expr_Value (Priority_Expr)));
         else
            return Priority_Value'(Kind => Nonstatic, Value => Dummy);
         end if;

      else
         if Present (Get_Rep_Item (Typ, Name_Interrupt_Priority)) then
            return
              Priority_Value'(Kind => Last_Interrupt_Prio, Value => Dummy);

         elsif Has_Attach_Handler (Typ) or else Has_Interrupt_Handler (Typ)
         then
            return
              Priority_Value'(Kind => Default_Interrupt_Prio, Value => Dummy);

         else
            return Priority_Value'(Kind => Default_Prio, Value => Dummy);
         end if;
      end if;
   end Protected_Type_Priority;

   ----------------------------------
   -- GG_Register_Protected_Object --
   ----------------------------------

   procedure GG_Register_Protected_Object
     (PO : Entity_Id; PT : Entity_Id; Prio : Priority_Value)
   is
      procedure Serialize is new
        Flow_Generated_Globals.Phase_1.Write.Serialize_Discrete
          (Priority_Kind);
   begin
      New_GG_Line (EK_Protected_Instance);
      Serialize (PT);
      Serialize (PO);
      Serialize (Prio.Kind);
      if Prio.Kind = Static then
         Serialize (Prio.Value);
      end if;
      Terminate_GG_Line;
   end GG_Register_Protected_Object;

   ----------------------
   -- Register_PO_Info --
   ----------------------

   procedure Register_PO_Info (PO : Entity_Id; PT : Entity_Id; Prefix : String)
   is
   begin
      if Is_Protected_Type (PT) then
         --  Register the protected object in the ALI file. Note that we'll
         --  record its first subtype as opposed to the actual type to make
         --  sure it works also with discriminated types. In the latter case
         --  the actual type is an Itype.
         GG_Register_Protected_Object
           (PO, First_Subtype (PT), Protected_Type_Priority (PT));

         declare
            Ent : Entity_Id := First_Entity (PT);

         begin
            --  Register value of Max_Queue_Length for an entry

            while Present (Ent) loop
               if Ekind (Ent) = E_Entry and then Entity_In_SPARK (Ent) then
                  declare
                     Max_Queue_Length : constant Nat :=
                       UI_To_Int (Get_Max_Queue_Length (Ent));
                     --  Zero is returned when the pragma is not
                     --  present and it stands for unbounded queue
                     --  length.

                  begin
                     GG_Register_Max_Queue_Length
                       (Prefix & "__" & Get_Name_String (Chars (Ent)),
                        Max_Queue_Length);
                  end;
               end if;
               Next_Entity (Ent);
            end loop;
         end;

      elsif Is_Record_Type (PT) then
         declare
            C : Entity_Id := First_Component (PT);

         begin
            while Present (C)
              and then Component_Is_Visible_In_SPARK (C)
              and then Entity_In_SPARK (Etype (C))
            loop
               Register_PO_Info
                 (PO, Etype (C), Prefix & "__" & Get_Name_String (Chars (C)));
               Next_Component (C);
            end loop;
         end;

      elsif Is_Array_Type (PT) then
         Register_PO_Info (PO, Component_Type (PT), Prefix);
      end if;
   end Register_PO_Info;

   -------------------------------------
   -- GG_Register_Protected_Operation --
   -------------------------------------

   procedure GG_Register_Protected_Operation (Op : Entity_Id) is
      Parent_Type : constant Entity_Id := Scope (Op);

   begin
      New_GG_Line (EK_Protected_Operation);
      Serialize (Op);
      Serialize (Parent_Type);
      Terminate_GG_Line;
   end GG_Register_Protected_Operation;

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

   procedure GG_Register_Task_Object
     (Typ : Entity_Id; Object : Entity_Id; Instances : Instance_Number) is
   begin
      New_GG_Line (EK_Task_Instance);
      Serialize (Typ);
      Serialize (Object);
      Serialize (Instances);
      Terminate_GG_Line;
   end GG_Register_Task_Object;

   ---------------------------
   -- Register_Synchronized --
   ---------------------------

   procedure Register_Synchronized (E : Entity_Id) is
   begin
      if Is_Library_Level_Entity (E) and then Is_Synchronized (E) then
         Synchronized_Vars.Include (E);
      end if;
   end Register_Synchronized;

   -----------------------
   -- Register_Volatile --
   -----------------------

   procedure Register_Volatile (E : Entity_Id) is
   begin
      --  Only register truly volatile objects, i.e. not constants of a
      --  volatile type (that may only come from code with SPARK_Mode => Off),
      --  because they only act as snapshots of some truly volatile objects.
      if Has_Volatile (E) and then Ekind (E) /= E_Constant then
         if Has_Volatile_Property (E, Pragma_Async_Readers) then
            Async_Readers_Vars.Include (E);

            if Has_Volatile_Property (E, Pragma_Effective_Writes) then
               Effective_Writes_Vars.Include (E);
            end if;
         end if;

         if Has_Volatile_Property (E, Pragma_Async_Writers) then
            Async_Writers_Vars.Include (E);

            if Has_Volatile_Property (E, Pragma_Effective_Reads) then
               Effective_Reads_Vars.Include (E);
            end if;
         end if;
      end if;
   end Register_Volatile;

   -----------------------
   -- GG_Write_Finalize --
   -----------------------

   procedure GG_Write_Finalize is
   begin
      --  The remaining entries are not specific to individual entities; it is
      --  the minimum information for objects (possibly from other compilation
      --  for which we will not have an ALI file at all, e.g. predefined units)
      --  that is needed in phase 2.

      if not Remote_States.Is_Empty then
         New_GG_Line (EK_Remote_States);
         Serialize (Remote_States);
         Terminate_GG_Line;
      end if;

      if not Predefined_Initialized_Entities.Is_Empty then
         New_GG_Line (EK_Predef_Init_Entities);
         Serialize (Predefined_Initialized_Entities);
         Terminate_GG_Line;
      end if;

      if not Async_Readers_Vars.Is_Empty
        or else not Async_Writers_Vars.Is_Empty
        or else not Effective_Reads_Vars.Is_Empty
        or else not Effective_Writes_Vars.Is_Empty
      then
         New_GG_Line (EK_Volatiles);
         Serialize (Async_Readers_Vars, "AR");
         Serialize (Async_Writers_Vars, "AW");
         Serialize (Effective_Reads_Vars, "ER");
         Serialize (Effective_Writes_Vars, "EW");
         Terminate_GG_Line;
      end if;

      if not Synchronized_Vars.Is_Empty then
         New_GG_Line (EK_Synchronized);
         Serialize (Synchronized_Vars);
         Terminate_GG_Line;
      end if;

      if not Checked_Ghost_Entities.Is_Empty then
         New_GG_Line (EK_Checked_Ghost_Entities);
         Serialize (Checked_Ghost_Entities);
         Terminate_GG_Line;
      end if;

      if not Ignored_Ghost_Entities.Is_Empty then
         New_GG_Line (EK_Ignored_Ghost_Entities);
         Serialize (Ignored_Ghost_Entities);
         Terminate_GG_Line;
      end if;

      if not Constants.Is_Empty then
         New_GG_Line (EK_Constants);
         Serialize (Constants);
         Terminate_GG_Line;
      end if;

      if not CAE_Entities.Is_Empty then
         New_GG_Line (EK_CAE_Entities);
         Serialize (CAE_Entities);
         Terminate_GG_Line;
      end if;

      for PO of Protected_Objects loop
         Register_PO_Info (PO, Etype (PO), Unique_Name (PO));
      end loop;

      for Op of Protected_Operations loop
         GG_Register_Protected_Operation (Op);
      end loop;

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

   ----------------------------
   -- GG_Register_Flow_Scope --
   ----------------------------

   procedure GG_Register_Flow_Scope (E : Entity_Id; Info : Hierarchy_Info_T) is
      procedure Serialize is new Serialize_Discrete (Boolean);
      procedure Serialize is new Serialize_Discrete (Declarative_Part);

   begin
      New_GG_Line (EK_Flow_Scope);

      Serialize (E);
      Serialize (Info.Is_Package);
      Serialize (Info.Is_Private);

      Serialize (Present (Info.Instance_Parent));
      if Present (Info.Instance_Parent) then
         Serialize (Info.Instance_Parent);
      end if;

      Serialize (Present (Info.Template));
      if Present (Info.Template) then
         Serialize (Info.Template);
      end if;

      Serialize (Present (Info.Container.Ent));
      if Present (Info.Container.Ent) then
         Serialize (Info.Container.Ent);
         Serialize (Info.Container.Part);
      else
         Serialize (Info.Parent);
      end if;

      Terminate_GG_Line;

      if Ekind (E) = E_Package and then Has_Non_Null_Abstract_State (E) then
         for State of Iter (Abstract_States (E)) loop
            declare
               Part_Ofs : constant Elist_Id := Part_Of_Constituents (State);
            begin
               if Present (Part_Ofs)
                 and then not Is_Empty_Elmt_List (Part_Of_Constituents (State))
               then
                  New_GG_Line (EK_Part_Of);
                  Serialize (State);
                  Serialize (Part_Of_Constituents (State));
                  Terminate_GG_Line;
               end if;
            end;
         end loop;
      end if;
   end GG_Register_Flow_Scope;

end Flow_Generated_Globals.Phase_1;
