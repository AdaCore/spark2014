-- Proximity fuze implementation
--
-- $Log: fuze.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/08/17 15:07:48  adi
-- Added check that new arm data is fresh
--
-- Revision 1.2  2003/08/17 14:58:35  adi
-- Updated to read back info from bus
--
-- Revision 1.1  2003/08/17 14:17:06  adi
-- Initial revision
--
--
with Clock_Utils,SystemTypes;
with Bus,RT1553,IBIT,Bit_Machine;
package body Fuze
  --# own State is
  --#     current_state,
  --#     state_timer,
  --#     BIT_State;
is
   -- The current action state of the fuze
   Current_State : State_Types.Fuze := State_Types.Unarmed;
   -- What time the fuze state last changed
   State_timer  : Clock.Millisecond := Clock.Millisecond'First;
   -- The BIT state
   Bit_State  : Bit_Machine.Machine := Bit_Machine.Initial_Machine;

   Bus_Id : constant Rt1553.Lru_Name := Rt1553.Fuze;

   -- maximum times to remain in states
   type Time_Array is array(State_Types.Fuze) of Clock.Millisecond;
   Max_State_Time : constant Time_Array
     := Time_Array'(State_Types.Unarmed    =>      0,
                    State_Types.Arming     =>  3_000,
                    State_Types.Live       =>      0,
                    State_Types.Triggering =>  2_000,
                    State_Types.Timed_Out  =>      0);
   type State_Change_Array is array(State_Types.Fuze) of
     State_Types.Fuze;
   State_Change : constant State_Change_Array :=
     State_Change_Array'(State_Types.Unarmed    => State_Types.Unarmed,
                         State_Types.arming     => State_Types.live,
                         State_Types.live       => State_Types.live,
                         State_Types.triggering => State_Types.unarmed,
                         State_Types.Timed_Out  => State_Types.Timed_out);

   -- See whether the current state needs updating automatically
   procedure Update_State
     --# global in out current_state, state_timer;
     --#        in out clock.time;
     --# derives clock.time from *, current_state &
     --#         current_state, state_timer from
     --#         state_timer, clock.time, current_state;
   is
      T_Now,T_Delta : Clock.Millisecond;
      T_Valid : Boolean;
   begin
      T_Delta := Max_State_Time(Current_State);
      if T_Delta > 0 then
         Clock.Read(T => T_Now,
                    Valid => T_Valid);
         if T_Valid and then
           State_Timer < T_Now and then
           (T_Now - State_Timer) >= T_Delta then
            -- Time is valid and enough has passed
            State_Timer := T_Now;
            Current_State := State_Change(Current_State);
         else
            -- Can't change state as no time known
            null;
         end if;
      else
         -- No automatic change
         null;
      end if;
   end Update_State;


   --------- Public subprograms

   procedure Set_state(New_state : in State_Types.fuze)
     --# global    out current_state, state_timer;
     --#           in out clock.time;
     --# derives current_state from new_state, clock.time &
     --#         clock.time from * &
     --#         state_timer from clock.time;
   is
      Time_Valid : Boolean;
   begin
      Current_State := New_State;
      Clock.Read(State_timer,Time_Valid);
      if not Time_Valid then
         -- This is OK for now
         Current_State := New_State;
      end if;
   end Set_state;

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle
     --# global in out current_state, state_timer;
     --#        in out BIT_State;
     --#        in out Clock.Time;
     --#        in Bus.Outputs;
     --#        in out Bus.Inputs;
     --# derives
     --#        BIT_State
     --#          from *, Bus.Outputs &
     --#        Bus.Inputs from *, Clock.Time,
     --#        current_state, state_timer,
     --#        BIT_State &
     --#        Clock.Time from *, current_state, bus.outputs,
     --#                    state_timer &
     --#        current_state from *, clock.time, state_timer,
     --#                bus.outputs &
     --#        state_timer from *, clock.time, current_state,
     --#                bus.outputs;
   is
      Datum : Bus.Word;
      New_State : State_Types.Fuze;
   begin
      Update_State;
      -- Write the state info to T1 word 1
      Rt1553.Write_Word(Data =>
                          State_Types.Fuze_Values(Current_State),
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
         -- Read in armament control data
         -- Read a new state value off R1 word 1
         Rt1553.Read_Word(Src => Bus_id,
                          Idx => 1,
                          Subaddress_Idx => 1,
                          Data => Datum);
         if Datum /= 0 then
            New_State := State_Types.Fuze_Action(Datum);
            if New_State /= Current_State then
               -- State change commanded
               Set_State(New_State);
            end if;
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
   --# global    out state_timer;
   --# derives state_timer from ms;
   is begin
      State_Timer := Ms;
   end Set_timer;

   -- Read the current state
   procedure Read_state(This_State : out State_Types.Fuze)
     --# global in     current_state;
     --# derives this_state from current_state;
   is
   begin
      This_State := Current_State;
   end Read_state;

   procedure Fail_Next_Bit
     --# global in out BIT_State;
     --# derives BIT_State from *;
   is begin
      BIT_Machine.Fail_Next(Bit_State);
   end Fail_Next_Bit;

   procedure Init
     --# global out current_state, state_timer, BIT_State;
     --#        in out Bus.Inputs;
     --# derives current_state, state_timer, BIT_State from &
     --#        Bus.Inputs from *;
   is begin
      -- Initialise the bus message 1T
      RT1553.Set_Message_Valid(Subaddress_Idx => 1,
                               Src => Bus_id);
      -- Initialise the variables
      Current_State := State_Types.Unarmed;
      State_Timer   := Clock.Millisecond'First;
      BIT_Machine.Create(Ticks_To_Complete => 30,
                         State => Bit_State);
   end Init;

   procedure Command is separate;
end Fuze;
