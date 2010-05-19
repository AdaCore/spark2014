-- Self-destruct implementation
--
-- $Log: destruct.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 19:15:39  adi
-- Initial revision
--
--
with Clock_Utils,SystemTypes;
with Bus,RT1553,IBIT,Bit_Machine;
package body Destruct
  --# own State is
  --#     current_stage,
  --#     stage_timer,
  --#     BIT_State;
is
   -- The current action state of the destruct
   Current_Stage : Stage := Destruct_Cfg.inactive;
   -- What time the destruct state last changed
   stage_timer  : Clock.Millisecond := Clock.Millisecond'First;
   -- The BIT state
   Bit_State  : Bit_Machine.Machine := Bit_Machine.Initial_Machine;

   Bus_Id : constant Rt1553.Lru_Name := Rt1553.Destruct;

   -- maximum times to remain in states
   type Time_Array is array(Stage) of Clock.Millisecond;
   Max_Stage_Time : constant Time_Array
     := Time_Array'(Destruct_Cfg.Inactive  => 0,
                    Destruct_Cfg.Armed     => 20_000,
                    Destruct_Cfg.Detonated => 0);

   -- See whether the current stage needs updating automatically
   procedure Update_Stage
     --# global in out current_stage, stage_timer;
     --#        in out clock.time;
     --# derives clock.time from *, current_stage &
     --#         current_stage, stage_timer from
     --#         stage_timer, clock.time, current_stage;
   is
      T_Now,T_Delta : Clock.Millisecond;
      T_Valid : Boolean;
   begin
      T_Delta := Max_Stage_Time(Current_Stage);
      if T_Delta > 0 then
         Clock.Read(T => T_Now,
                    Valid => T_Valid);
         if T_Valid and then
           Stage_Timer < T_Now and then
           (T_Now - Stage_Timer) >= T_Delta then
            -- Time is valid and enough has passed
            Stage_Timer := T_Now;
            -- Always resets to Inactive for safety reasons
            Current_Stage := Destruct_Cfg.inactive;
         else
            -- Can't change state as no time known
            null;
         end if;
      else
         -- No automatic change
         null;
      end if;
   end Update_Stage;


   --------- Public subprograms

   procedure Set_stage(New_stage : in Stage)
     --# global    out current_stage, stage_timer;
     --#           in out clock.time;
     --# derives current_stage from new_stage, clock.time &
     --#         clock.time from * &
     --#         stage_timer from clock.time;
   is
      Time_Valid : Boolean;
   begin
      Current_Stage := New_Stage;
      Clock.Read(stage_timer,Time_Valid);
      if not Time_Valid then
         -- This is OK for now
         Current_Stage := New_Stage;
      end if;
   end Set_stage;

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle
     --# global in out current_stage, stage_timer;
     --#        in out BIT_State;
     --#        in out Clock.Time;
     --#        in Bus.Outputs;
     --#        in out Bus.Inputs;
     --# derives
     --#        BIT_State
     --#          from *, Bus.Outputs &
     --#        Bus.Inputs from *, Clock.Time,
     --#        current_stage, stage_timer,
     --#        BIT_State &
     --#        Clock.Time from *, current_stage, stage_timer, bus.outputs
     --#                    &
     --#        current_stage from *, clock.time, stage_timer,
     --#                bus.outputs &
     --#        stage_timer from *, clock.time, current_stage,
     --#                bus.outputs;
   is
      Datum : Bus.Word;
      New_Stage : stage;
   begin
      Update_Stage;
      -- Write the stage info to T1 word 1
      Rt1553.Write_Word(Data =>
                          Destruct_cfg.State_To_code(Current_Stage),
                        Idx => 1,
                        Subaddress_Idx => 1,
                        Src => Bus_Id);
      -- Write the BIT phase to T1 word 2
      Rt1553.Write_Word(Data =>
                          IBIT.Phase_Lookup(BIT_Machine.Phase(Bit_State)),
                       Idx => 2,
                       Subaddress_Idx => 1,
                        Src => Bus_id);
      if Rt1553.Is_Valid(Src => Bus_Id,
                         Subaddress_Idx => 1) and then
        Rt1553.Is_Fresh(Src => Bus_Id,
                        Subaddress_Idx => 1) then
         -- Read a new stage value off R1 word 1
         Rt1553.Read_Word(Src => Bus_id,
                          Idx => 1,
                          Subaddress_Idx => 1,
                          Data => Datum);
         if Destruct_Cfg.Code_To_State(Datum) /=
           Current_Stage then
            New_Stage := Destruct_Cfg.Transition(Old_State => Current_Stage,
                                                New_Code  => Datum);
            Set_Stage(New_Stage);
         end if;
      end if;
      -- Read the BIT info off R1 word 2
      Rt1553.Read_Word(Src => Bus_id,
                       Idx => 2,
                       Subaddress_Idx => 1,
                       Data => Datum);
      BIT_Machine.Change_State(Word => Datum,
                               State => Bit_state);
      -- And cycle the BIT
      BIT_Machine.Step(Bit_State);
   end Cycle;


   -- Set the current state timer
   procedure Set_timer(Ms : in Clock.Millisecond)
   --# global    out stage_timer;
   --# derives stage_timer from ms;
   is begin
      Stage_Timer := Ms;
   end Set_timer;

   -- Read the current stage
   procedure Read_stage(This_Stage : out Stage)
     --# global in     current_stage;
     --# derives this_stage from current_stage;
   is
   begin
      This_Stage := Current_Stage;
   end Read_stage;

   procedure Fail_Next_Bit
     --# global in out BIT_State;
     --# derives BIT_State from *;
   is begin
      BIT_Machine.Fail_Next(Bit_State);
   end Fail_Next_Bit;

   procedure Init
     --# global out current_stage, stage_timer, BIT_State;
     --#        in out Bus.Inputs;
     --# derives current_stage, stage_timer, BIT_State from &
     --#        Bus.Inputs from *;
   is begin
      -- Initialise the bus message 1T
      RT1553.Set_Message_Valid(Subaddress_Idx => 1,
                               Src => Bus_id);
      -- Initialise the variables
      Current_Stage := Destruct_Cfg.inactive;
      Stage_Timer   := Clock.Millisecond'First;
      BIT_Machine.Create(Ticks_To_Complete => 9,
                         State => Bit_State);
   end Init;

   procedure Command is separate;
end Destruct;
