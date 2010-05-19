-- Motor implementation
--
-- $Log: motor.adb,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 18:19:00  adi
-- Initial revision
--
--
with
  Clock_Utils,
  Systemtypes,
  Bus,
  RT1553,
  IBIT,
  Measuretypes.Encode,
  Measuretypes.Decode,
  Bit_Machine;
package body Motor
  --# own State is
  --#     current_thrust,
  --#     commanded_thrust,
  --#     command_time,
  --#     BIT_State;
is
   subtype Integer32 is Systemtypes.Integer32;

   -- The current and commanded thrust
   Current_thrust : Power := Power'first;
   Commanded_Thrust : Power := Power'first;

   -- What time the angle was last requested for each fin
   Command_Time : Clock.millisecond := 0;

   -- The BIT state
   Bit_State  : Bit_Machine.Machine := Bit_Machine.Initial_Machine;

   Bus_Id : constant Rt1553.Lru_Name := Rt1553.motor;

   -- Extrapolate the actual thrust
   procedure Extrapolate_thrust(New_Thrust : out Power)
     --# global in out clock.time;
     --#        in current_thrust, commanded_thrust, command_time;
     --# derives
     --#     clock.time from * &
     --#     new_thrust from
     --#        clock.time,
     --#        current_thrust,
     --#        commanded_thrust,
     --#        command_time;
   is
      Now : Clock.Millisecond;
      Time_Valid : Boolean;
      Diff_Time : Clock.Millisecond;
      Tmp : Integer32;
      begin
      Clock.Read(T => Now,Valid => Time_Valid);
      if Current_thrust = Commanded_thrust then
         New_thrust := Current_thrust;
      elsif Time_Valid then
         Diff_Time := Now - Command_Time;
         if Diff_Time < 0 then
            -- No movement
            New_Thrust := Current_Thrust;
         else
            if Diff_Time > 30_000 then
               -- Max response is under 30 seconds anyway
               Diff_Time := 30_000;
            end if;
            -- Work out the thrust extrapolated
            if Commanded_thrust >= Current_thrust then
               Tmp := Integer32(Current_thrust) +
                 (Integer32(Diff_Time) * Motor_Cfg.burn_Rate) / 1000;
               if Tmp > Integer32(Commanded_thrust) then
                  New_thrust := Commanded_Thrust;
               else
                  New_thrust := power(Tmp);
               end if;
            else
               -- target < current
               Tmp := Integer32(Current_thrust) -
                 (Integer32(Diff_Time) * Motor_Cfg.burn_Rate) / 1000;
               if Tmp < Integer32(Commanded_thrust) then
                  New_Thrust := Commanded_thrust;
               else
                  New_thrust := power(Tmp);
               end if;
            end if;
         end if;
      else
         -- Can't estimate, return the current value
         New_thrust := Current_thrust;
      end if;
   end Extrapolate_thrust;


   --------- Public subprograms

   procedure Set_thrust(New_Level : in Power)
     --# global in out
     --#     current_thrust,
     --#     commanded_thrust,
     --#     command_time,
     --#     clock.time;
     --# derives
     --#     current_thrust from
     --#         *,
     --#         commanded_thrust,
     --#         command_time,
     --#         clock.time &
     --#     commanded_thrust from
     --#         new_level &
     --#     command_time from
     --#         clock.time &
     --#     clock.time from
     --#         *;
   is
      Time_Valid : Boolean;
      T : Clock.Millisecond;
      p : power;
   begin
      -- Update the fin's current angle
      Extrapolate_thrust(New_Thrust => p);
      Current_Thrust := p;
      Commanded_Thrust := New_level;
      Clock.Read(T => T,Valid => Time_Valid);
      if Time_Valid then
         Command_Time := T;
      else
         Command_Time := 0;
      end if;
   end Set_thrust;


   procedure Read_thrust(This_Level : out Power)
     --# global in out clock.time;
     --#     in current_thrust,
     --#     commanded_thrust,
     --#     command_time;
     --# derives
     --#     this_level from
     --#         current_thrust,
     --#         commanded_thrust,
     --#         command_time,
     --#         clock.time &
     --#     clock.time from
     --#         *;
   is
   begin
      Extrapolate_thrust(New_thrust => This_level);
   end Read_thrust;


   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle
     --# global in out current_thrust, commanded_thrust, command_time;
     --#        in out BIT_State;
     --#        in out Clock.Time;
     --#        in Bus.Outputs;
     --#        in out Bus.Inputs;
     --# derives
     --#     BIT_State from
     --#        *, Bus.Outputs &
     --#     Bus.Inputs from
     --#        *, Clock.Time,
     --#        current_thrust,
     --#        commanded_thrust,
     --#        command_time,
     --#        BIT_State &
     --#     Clock.Time from
     --#        current_thrust,
     --#        clock.time,
     --#        bus.outputs &
     --#     current_thrust from
     --#        clock.time,
     --#        command_time,
     --#        current_thrust,
     --#        commanded_thrust,
     --#        bus.outputs &
     --#     commanded_thrust from
     --#        current_thrust,
     --#        commanded_thrust,
     --#        bus.outputs &
     --#     command_time from
     --#        *,
     --#        clock.time,
     --#        current_thrust,
     --#        bus.outputs;
   is
      Datum, Dlo, Dhi : Bus.Word;
      P : Power;
   begin
      -- Write the thrust out to T1 word 1
      Extrapolate_thrust(New_Thrust => p);
      Measuretypes.Encode.Newton(N => P,
                                 Lo => Dlo,
                                 Hi => dhi);
      Rt1553.Write_Word(Data => Dlo,
                        Idx => 1,
                        Subaddress_Idx => 1,
                        Src => Bus_Id);
      Rt1553.Write_Word(Data => Dhi,
                        Idx => 2,
                        Subaddress_Idx => 1,
                        Src => Bus_Id);

      -- Write the BIT phase to T1 word 3
      Rt1553.Write_Word(Data =>
                          IBIT.Phase_Lookup(BIT_Machine.Phase(Bit_State)),
                        Idx => 3,
                        Subaddress_Idx => 1,
                        Src => Bus_id);

      -- Look for commands on R1
      if Rt1553.Is_Valid(Src => Bus_Id,
                         Subaddress_Idx => 1) and then
        Rt1553.Is_Fresh(Src => Bus_Id,
                        Subaddress_Idx => 1) then
         -- Read a new thrust off R1
         Rt1553.Read_Word(Src => Bus_id,
                          Idx => 1,
                          Subaddress_Idx => 1,
                          Data => dlo);
         Rt1553.Read_Word(Src => Bus_id,
                          Idx => 2,
                          Subaddress_Idx => 1,
                          Data => dhi);
         p := measuretypes.Decode.newton(Lo => Dlo, Hi => dhi);
         if p /= Current_Thrust Then
            Set_Thrust(P);
         end if;
      end if;

      -- Read the BIT info off R1 word 3
      Rt1553.Read_Word(Src => Bus_id,
                       Idx => 3,
                       Subaddress_Idx => 1,
                       Data => Datum);
      BIT_Machine.Change_State(Word => Datum,
                               State => Bit_state);
      -- And cycle the BIT
      BIT_Machine.Step(Bit_State);
   end Cycle;


   procedure Fail_Next_Bit
     --# global in out BIT_State;
     --# derives BIT_State from *;
   is begin
      BIT_Machine.Fail_Next(Bit_State);
   end Fail_Next_Bit;

   procedure Init
     --# global out current_thrust,
     --#            commanded_thrust,
     --#            command_time,
     --#            BIT_State;
     --#        in out Bus.Inputs;
     --# derives current_thrust,
     --#        commanded_thrust,
     --#        command_time,
     --#        BIT_State from &
     --#        Bus.Inputs from *;
   is begin
      -- Initialise the bus message 1T
      RT1553.Set_Message_Valid(Subaddress_Idx => 1,
                               Src => Bus_id);
      -- Initialise the variables
      Current_thrust := Power'first;
      Commanded_Thrust := Power'first;
      Command_time := 0;
      BIT_Machine.Create(Ticks_To_Complete => 23,
                         State => Bit_State);
   end Init;

   procedure Command is separate;
end Motor;
