-- Barometer simulator implementation
--
-- $Log: barometer.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.6  2003/08/06 20:41:33  adi
-- Use bit_machine
--
-- Revision 1.5  2003/02/19 19:04:56  adi
-- Details for Command proc
--
-- Revision 1.4  2003/02/12 23:29:06  adi
-- Corrected
--
-- Revision 1.3  2003/02/12 23:11:05  adi
-- Added init routine
--
-- Revision 1.2  2003/02/11 20:49:48  adi
-- Updated BIT package to use standard IBIT stuff
--
-- Revision 1.1  2003/02/10 20:06:45  adi
-- Initial revision
--
--
with Clock_Utils,SystemTypes;
with Bus,RT1553,IBIT,Bit_Machine;
package body Barometer
  --# own State is
  --#     Last_Altitude,
  --#     Last_Time,
  --#     Last_Velocity,
  --#     BIT_State;
is
   subtype Pos_Meter is MeasureTypes.Pos_Meter;

   Last_Altitude : Meter := 0;
   Last_Time     : Clock.Millisecond := Clock.Millisecond'First;
   Last_Velocity : Meter_Per_Sec := 0;
   Bit_State : Bit_Machine.Machine := Bit_Machine.Initial_Machine;

   -- Work out the current height.
   -- Note that it can't be < 0, so forget
   -- firing this thing from Death Valley.
   procedure Extrapolate_Height(Height : out Pos_Meter)
     --# global in     Last_Altitude, Last_Velocity, Last_Time;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         Height from Clock.Time, Last_Altitude,
     --#         Last_Velocity, Last_Time;
   is
      Time_Now,T_Delta : Clock.Millisecond;
      Time_Valid : Boolean;
      H_Delta,Temp_Height : Meter;
      VMS : Clock.Millisecond;
   begin
      Clock.Read(T => Time_Now,
                 Valid => Time_Valid);
      if not Time_Valid then
        -- Can't extrapolate
        Height := 0;
      else
         -- How many seconds change
         T_Delta := Clock_Utils.Delta_Time(Last_Time,Time_Now);
         if Last_Velocity < 0 then
            VMS := Clock.Millisecond(-Last_Velocity);
            H_Delta := -Meter((VMS * T_Delta)/1000);
         else
            VMS := Clock.Millisecond(Last_Velocity);
            H_Delta := Meter((VMS * T_Delta)/1000);
         end if;
         Temp_Height := Last_Altitude + H_Delta;
         if Temp_Height < 0 then
            Height := 0;
         else
            Height := Temp_Height;
         end if;
      end if;
   end Extrapolate_Height;

   --------- Public subprograms

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle
     --# global in Last_Altitude, Last_Time, Last_Velocity;
     --#        in out BIT_State;
     --#        in out Clock.Time;
     --#        in Bus.Outputs;
     --#        in out Bus.Inputs;
     --# derives
     --#        BIT_State
     --#          from *, Bus.Outputs &
     --#        Bus.Inputs from *, Clock.Time, Last_Altitude, Last_Time,
     --#        Last_Velocity, BIT_State &
     --#        Clock.Time from *;
   is
      Altitude : Pos_Meter;
      Datum : Bus.Word;
   begin
      Extrapolate_Height(Altitude);
      -- Write the altitude hi info to T1 word 1
      Rt1553.Write_Word(Data => Bus.Word(Altitude / 256),
                        Idx  => 1,
                        Subaddress_Idx => 1,
                        Src => RT1553.Barometer);
      -- Write the altitude low info to T1 word 2
      Rt1553.Write_Word(Data => Bus.Word(Altitude mod 256),
                        Idx  => 2,
                        Subaddress_Idx => 1,
                        Src => RT1553.Barometer);
      -- Write the BIT phase to T1 word 3
      Rt1553.Write_Word(Data => IBIT.Phase_Lookup(BIT_Machine.Phase(Bit_State)),
                       Idx => 3,
                       Subaddress_Idx => 1,
                       Src => RT1553.Barometer);
      -- Read the BIT info off R1
      Rt1553.Read_Word(Src => Rt1553.Barometer,
                       Idx => 1,
                       Subaddress_Idx => 1,
                       Data => Datum);
      BIT_Machine.Change_State(Word => Datum,
                               State => Bit_state);
      -- And cycle the BIT
      BIT_Machine.Step(Bit_State);
   end Cycle;

   -- Set the current altitude profile and
   -- vertical velocity
   procedure Set_Altitude_Profile(Height : in Meter;
                                  DZ     : in Meter_Per_Sec)
   --# global    out Last_Altitude, Last_Time, Last_Velocity;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_Altitude from Height &
   --#         Last_Time     from Clock.Time &
   --#         Last_Velocity    from DZ, Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_Altitude := Height;
      Last_Velocity := DZ;
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_Velocity := 0;
      end if;
   end Set_Altitude_Profile;

   -- Read the current altitude
   procedure Read_Altitude(Height : out Meter)
     --# global in     Last_Altitude, Last_Time, Last_Velocity;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         Height from Last_Altitude, Last_Time, Last_Velocity,
     --#         Clock.Time;
   is
   begin
      Extrapolate_Height(Height);
   end Read_Altitude;

   procedure Fail_Next_Bit
     --# global in out BIT_State;
     --# derives BIT_State from *;
   is begin
      BIT_Machine.Fail_Next(Bit_State);
   end Fail_Next_Bit;

   procedure Init
     --# global out Last_Altitude, Last_Time, Last_Velocity, BIT_State;
     --#        in out Bus.Inputs;
     --# derives Last_Altitude, Last_Time, Last_Velocity, BIT_State from &
     --#        Bus.Inputs from *;
   is begin
      -- Initialise the bus message 1T
      RT1553.Set_Message_Valid(Subaddress_Idx => 1,
                               Src => RT1553.Barometer);
      -- Initialise the variables
      Last_Altitude := 0;
      Last_Time     := Clock.Millisecond'First;
      Last_Velocity := 0;
      BIT_Machine.Create(Ticks_To_Complete => 10,
                         State => Bit_State);
   end Init;

   procedure Command is separate;
end Barometer;
