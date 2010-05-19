-- Airspeed simulator implementation
--
-- $Log: airspeed.adb,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/08 20:45:17  adi
-- Initial revision
--
--
--
with Clock_Utils,SystemTypes;
with Bus,RT1553,IBIT,Bit_Machine;
package body Airspeed
  --# own State is
  --#     Last_Speed,
  --#     Last_Accel,
  --#     Last_Time,
  --#     BIT_State;
is
   Last_Speed : Meter_Per_Sec := 0;
   Last_Accel : cm_Per_Sec_2 := 0;
   Last_Time     : Clock.Millisecond := Clock.Millisecond'First;
   Bit_State : Bit_Machine.Machine := Bit_Machine.Initial_Machine;

   -- Work out the current speed.
   procedure Extrapolate_Speed(Speed : out Meter_Per_sec)
     --# global in     Last_Speed, Last_Accel, Last_Time;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         Speed from Clock.Time, Last_Speed,
     --#         Last_Accel, Last_Time;
   is
      Time_Now,T_Delta : Clock.Millisecond;
      Time_Valid : Boolean;
      S_Delta : Meter_Per_Sec;
      VMS : Clock.Millisecond;
   begin
      Clock.Read(T => Time_Now,
                 Valid => Time_Valid);
      if not Time_Valid then
        -- Can't extrapolate
        Speed := 0;
      else
         -- How many seconds change
         T_Delta := Clock_Utils.Delta_Time(Last_Time,Time_Now);
         if Last_accel < 0 then
            VMS := Clock.Millisecond(-Last_accel);
            S_Delta := -Meter_Per_Sec((VMS * T_Delta)/100_000);
         else
            VMS := Clock.Millisecond(Last_accel);
            S_Delta := Meter_Per_Sec((VMS * T_Delta)/100_000);
         end if;
         Speed := Last_Speed + S_Delta;
      end if;
   end Extrapolate_Speed;

   --------- Public subprograms

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle
     --# global in Last_Speed, Last_Time, Last_Accel;
     --#        in out BIT_State;
     --#        in out Clock.Time;
     --#        in Bus.Outputs;
     --#        in out Bus.Inputs;
     --# derives
     --#        BIT_State
     --#          from *, Bus.Outputs &
     --#        Bus.Inputs from *, Clock.Time, Last_Speed, Last_Time,
     --#        Last_Accel, BIT_State &
     --#        Clock.Time from *;
   is
      Speed : Meter_Per_Sec;
      Datum : Bus.Word;
   begin
      Extrapolate_Speed(speed);
      -- Write the speed info to T1 word 1
      Rt1553.Write_Word(Data => Bus.Word(Speed),
                        Idx  => 1,
                        Subaddress_Idx => 1,
                        Src => RT1553.Asi);
      -- Ignore T1 word 2 for now
      -- Write the BIT phase to T1 word 3
      Rt1553.Write_Word(Data => IBIT.Phase_Lookup(BIT_Machine.Phase(Bit_State)),
                       Idx => 3,
                       Subaddress_Idx => 1,
                       Src => RT1553.Asi);
      -- Read the BIT info off R1
      Rt1553.Read_Word(Src => Rt1553.Asi,
                       Idx => 1,
                       Subaddress_Idx => 1,
                       Data => Datum);
      BIT_Machine.Change_State(Word => Datum,
                               State => Bit_state);
      -- And cycle the BIT
      BIT_Machine.Step(Bit_State);
   end Cycle;

   -- Set the current speed profile and accel
   procedure Set_airSpeed_Profile(Speed : in Meter_Per_sec;
                              Accel : in cm_Per_Sec_2)
   --# global    out Last_Speed, Last_Time, Last_Accel;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_Speed from Speed, Clock.Time &
   --#         Last_Time     from Clock.Time &
   --#         Last_Accel    from Accel, Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_Speed := speed;
      Last_Accel := Accel;
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_Speed := 0;
         Last_Accel := 0;
      end if;
   end Set_airSpeed_Profile;

   -- Read the current speed
   procedure Read_airSpeed(Speed : out Meter_Per_Sec)
     --# global in     Last_Speed, Last_Time, Last_Accel;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         Speed from Last_speed, Last_Time, Last_accel,
     --#         Clock.Time;
   is
   begin
      Extrapolate_Speed(Speed);
   end Read_airSpeed;

   -- Read the last-set acceleration and BIT status
   function Read_Accel return Cm_Per_Sec_2
     --# global in Last_Accel;
   is begin
      return Last_Accel;
   end Read_Accel;

   function Read_BIT_Status return Bit_Machine.Machine
     --# global in Bit_state;
   is begin
      return Bit_State;
   end Read_BIT_Status;


   procedure Fail_Next_Bit
     --# global in out BIT_State;
     --# derives BIT_State from *;
   is begin
      BIT_Machine.Fail_Next(Bit_State);
   end Fail_Next_Bit;

   procedure Init
     --# global out Last_Speed, Last_Time, Last_Accel, BIT_State;
     --#        in out Bus.Inputs;
     --# derives Last_Speed, Last_Time, Last_accel, BIT_State from &
     --#        Bus.Inputs from *;
   is begin
      -- Initialise the bus message 1T
      RT1553.Set_Message_Valid(Subaddress_Idx => 1,
                               Src => RT1553.Asi);
      -- Initialise the variables
      Last_Speed := 0;
      Last_Time     := Clock.Millisecond'First;
      Last_Accel := 0;
      BIT_Machine.Create(Ticks_To_Complete => 12,
                         State => Bit_State);
   end Init;

   procedure Command is separate;
end Airspeed;
