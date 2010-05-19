-- Steering implementation
--
-- $Log: steer.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/31 20:06:22  adi
-- Initial revision
--
--
with
  Clock_Utils,
  Systemtypes,
  Steer_Cfg.Encode,
  Steer_Cfg.Decode,
  Bus,
  RT1553,
  IBIT,
  Bit_Machine;
package body Steer
  --# own State is
  --#     current_angles,
  --#     commanded_angles,
  --#     command_times,
  --#     BIT_State;
is
   subtype Integer32 is Systemtypes.Integer32;

   type Fin_Angles is array(Fin) of Angle;
   Zero_Angles : constant Fin_Angles :=
     Fin_Angles'(others => 0);

   type Fin_Times is array(Fin) of Clock.Millisecond;
   Zero_Times : constant Fin_Times :=
     Fin_Times'(others => 0);

   -- The current and commanded angles of the steering fins
   Current_angles : Fin_Angles := Zero_angles;
   Commanded_Angles : Fin_Angles := Zero_Angles;

   -- What time the angle was last requested for each fin
   Command_Times : Fin_Times := Zero_Times;

   -- The BIT state
   Bit_State  : Bit_Machine.Machine := Bit_Machine.Initial_Machine;

   Bus_Id : constant Rt1553.Lru_Name := Rt1553.Fins;

   -- Extrapolate the actual angle of a fin
   procedure Extrapolate_Angle(For_Fin : in Fin;
                               New_Angle : out Angle)
     --# global in out clock.time;
     --#        in current_angles, commanded_angles, command_times;
     --# derives
     --#     clock.time from * &
     --#     new_angle from
     --#        for_fin,
     --#        clock.time,
     --#        current_angles,
     --#        commanded_angles,
     --#        command_times;
   is
      Current, Target : Angle;
      Now : Clock.Millisecond;
      Time_Valid : Boolean;
      Diff_Time : Clock.Millisecond;
      Tmp : Integer32;
   begin
      Clock.Read(T => Now,Valid => Time_Valid);
      Current := Current_Angles(For_Fin);
      Target  := Commanded_Angles(For_Fin);
      if Current = Target then
         New_Angle := Current;
      elsif Time_Valid then
         Diff_Time := Now - Command_Times(For_Fin);
         if Diff_Time < 0 then
            -- No movement
            New_Angle := Current;
         else
            if Diff_Time > 2_000 then
               -- Max response is under 1 second anyway
               Diff_Time := 2_000;
            end if;
            -- Work out the angle extrapolated
            if Target >= Current then
               Tmp := Integer32(Current) +
                 (Integer32(Diff_Time) * Steer_Cfg.Move_Rate) / 1000;
               if Tmp > Integer32(Target) then
                  New_angle := Target;
               else
                  New_Angle := Angle(Tmp);
               end if;
            else
               -- target < current
               Tmp := Integer32(Current) -
                 (Integer32(Diff_Time) * Steer_Cfg.Move_Rate) / 1000;
               if Tmp < Integer32(Target) then
                  New_Angle := Target;
               else
                  New_Angle := Angle(Tmp);
               end if;
            end if;
         end if;
      else
         -- Can't estimate, return the current value
         New_Angle := Current;
      end if;
   end Extrapolate_Angle;


   --------- Public subprograms

   procedure Set_deflection(For_Fin : in Fin;
                            New_Angle : in Angle)
     --# global in out
     --#     current_angles,
     --#     commanded_angles,
     --#     command_times,
     --#     clock.time;
     --# derives
     --#     current_angles from
     --#         *,
     --#         commanded_angles,
     --#         command_times,
     --#         clock.time,
     --#         for_fin &
     --#     commanded_angles from
     --#         *,
     --#         for_fin,
     --#         new_angle &
     --#     command_times from
     --#         *,
     --#         for_fin,
     --#         clock.time &
     --#     clock.time from
     --#         *;
   is
      Time_Valid : Boolean;
      T : Clock.Millisecond;
      A : Angle;
   begin
      -- Update the fin's current angle
      Extrapolate_Angle(For_Fin => For_Fin,
                        New_Angle => A);
      Current_Angles(For_Fin) := a;
      Commanded_Angles(For_Fin) := New_Angle;
      Clock.Read(T => T,Valid => Time_Valid);
      if Time_Valid then
         Command_Times(For_Fin) := T;
      else
         Command_Times(For_Fin) := 0;
      end if;
   end Set_deflection;


   procedure Read_deflection(For_Fin : in Fin;
                            this_Angle : out Angle)
     --# global in out clock.time;
     --#     in current_angles,
     --#     commanded_angles,
     --#     command_times;
     --# derives
     --#     this_angle from
     --#         current_angles,
     --#         commanded_angles,
     --#         command_times,
     --#         clock.time,
     --#         for_fin &
     --#     clock.time from
     --#         *;
   is
   begin
      Extrapolate_Angle(For_Fin => For_Fin,
                        New_Angle => This_Angle);
   end Read_deflection;


   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle
     --# global in out current_angles, commanded_angles, command_times;
     --#        in out BIT_State;
     --#        in out Clock.Time;
     --#        in Bus.Outputs;
     --#        in out Bus.Inputs;
     --# derives
     --#     BIT_State from
     --#        *, Bus.Outputs &
     --#     Bus.Inputs from
     --#        *, Clock.Time,
     --#        current_angles,
     --#        commanded_angles,
     --#        command_times,
     --#        BIT_State &
     --#     Clock.Time,
     --#     current_angles,
     --#     commanded_angles from
     --#        current_angles,
     --#        clock.time,
     --#        commanded_angles,
     --#        command_times,
     --#        bus.outputs &
     --#     command_times from
     --#        *, clock.time,
     --#        current_angles,
     --#        commanded_angles,
     --#        bus.outputs;
   is
      Datum : Bus.Word;

      procedure Write_Fin_Angle(F : in Fin;
                                I : in Bus.Word_Index)
        --# global
        --#        in out Clock.Time;
        --#        in out Bus.Inputs;
        --#        in current_angles, commanded_angles, command_times;
        --# derives
        --#    clock.time from
        --#        * &
        --#    bus.inputs from
        --#        *, f, I,
        --#        clock.time,
        --#        current_angles,
        --#        commanded_angles,
        --#        command_times;
      is
         A : Angle;
         B : Bus.Word;
      begin
         Extrapolate_Angle(For_Fin => F,
                           New_Angle => A);
         B := Steer_Cfg.Encode.Fin_angle(A);
         Rt1553.Write_Word(Data => B,
                           Idx => I,
                           Subaddress_Idx => 1,
                           Src => Bus_Id);
      end Write_Fin_Angle;

      procedure Read_Fin_Angle(F : in Fin;
                                I : in Bus.Word_Index)
        --# global in out
        --#    current_angles,
        --#    commanded_angles,
        --#    command_times;
        --#        in out Clock.Time;
        --#        in Bus.Outputs;
        --# derives
        --#    clock.time from
        --#       *, f, i,
        --#       current_angles,
        --#       bus.outputs &
        --#    current_angles from
        --#       *, f, I,
        --#       commanded_angles,
        --#       command_times,
        --#       clock.time,
        --#       bus.outputs &
        --#    commanded_angles from
        --#       *, f, I,
        --#       current_angles,
        --#       bus.outputs &
        --#    command_times from
        --#       *, f, I,
        --#       current_angles,
        --#       clock.time,
        --#       bus.outputs;
      is
         A : Angle;
         B : Bus.Word;
      begin
         -- Read a new state value off R1
         Rt1553.Read_Word(Src => Bus_id,
                          Idx => I,
                          Subaddress_Idx => 1,
                          Data => B);
         A := Steer_Cfg.Decode.Fin_angle(b);
         if A /= Current_Angles(F) Then
            -- Angle change
            Set_Deflection(For_Fin => F,
                           New_Angle => A);
         end if;
      end Read_Fin_Angle;

   begin
      -- Write the fin angles out to T1 words 1-4
      Write_Fin_Angle(F => Steer_Cfg.Port,
                      I => 1);
      Write_Fin_Angle(F => Steer_Cfg.Starboard,
                      I => 2);
      Write_Fin_Angle(F => Steer_Cfg.Top,
                      I => 3);
      Write_Fin_Angle(F => Steer_Cfg.Bottom,
                      I => 4);
      -- Write the BIT phase to T1 word 5
      Rt1553.Write_Word(Data =>
                          IBIT.Phase_Lookup(BIT_Machine.Phase(Bit_State)),
                        Idx => 5,
                        Subaddress_Idx => 1,
                        Src => Bus_id);
      -- Look for commands on R1
      if Rt1553.Is_Valid(Src => Bus_Id,
                         Subaddress_Idx => 1) and then
        Rt1553.Is_Fresh(Src => Bus_Id,
                        Subaddress_Idx => 1) then
         -- Read in new fin commands
         Read_Fin_Angle(F => Steer_Cfg.Port,
                        I => 1);
         Read_Fin_Angle(F => Steer_Cfg.Starboard,
                        I => 2);
         Read_Fin_Angle(F => Steer_Cfg.Top,
                        I => 3);
         Read_Fin_Angle(F => Steer_Cfg.Bottom,
                        I => 4);

      end if;
      -- Read the BIT info off R1 word 5
      Rt1553.Read_Word(Src => Bus_id,
                       Idx => 5,
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
     --# global out current_angles,
     --#            commanded_angles,
     --#            command_times,
     --#            BIT_State;
     --#        in out Bus.Inputs;
     --# derives current_angles,
     --#        commanded_angles,
     --#        command_times,
     --#        BIT_State from &
     --#        Bus.Inputs from *;
   is begin
      -- Initialise the bus message 1T
      RT1553.Set_Message_Valid(Subaddress_Idx => 1,
                               Src => Bus_id);
      -- Initialise the variables
      Current_angles := Zero_Angles;
      Commanded_Angles := Zero_Angles;
      Command_times := Zero_Times;
      BIT_Machine.Create(Ticks_To_Complete => 41,
                         State => Bit_State);
   end Init;

   procedure Command is separate;
end Steer;
