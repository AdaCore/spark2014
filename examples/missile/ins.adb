-- INS
--
-- $Log: ins.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/10 18:19:25  adi
-- Initial revision
--
--
--
with Clock_Utils,SystemTypes;
with Bus,RT1553,IBIT,Bit_Machine;
with Cartesian;
package body Ins
  --# own State is
  --#     Last_Position,
  --#     Last_Velocity,
  --#     Last_Time,
  --#     BIT_State;
is
   Last_Position : Cartesian.Position := Cartesian.Zero_Position;
   Last_Velocity : Cartesian.Velocity := Cartesian.Zero_Velocity;
   Last_Time     : Clock.Millisecond := Clock.Millisecond'First;
   Bit_State : Bit_Machine.Machine := Bit_Machine.Initial_Machine;

   Bus_Id : constant Rt1553.Lru_Name := Rt1553.Ins;

   -- Work out the current position.
   procedure Extrapolate_Position(Position : out Cartesian.position)
     --# global in     Last_Position, Last_Velocity, Last_Time;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         Position from Clock.Time, Last_Position,
     --#         Last_Velocity, Last_Time;
   is
      Time_Now,T_Delta : Clock.Millisecond;
      Time_Valid : Boolean;

      procedure Extrapolate_Dimension(O : in Meter;
                                      V : in Meter_Per_Sec;
                                      S : out Meter)
        --# global in t_delta;
        --# derives S from O, V, t_delta;
      is
         S_Delta : Meter;
         VMS : Clock.Millisecond;
      begin
         if v < 0 then
            VMS := Clock.Millisecond(-v);
            S_Delta := -Meter((VMS * T_Delta)/1000);
         else
            VMS := Clock.Millisecond(v);
            S_Delta := Meter((VMS * T_Delta)/1000);
         end if;
         S := O + S_Delta;
      end Extrapolate_Dimension;
   begin
      Clock.Read(T => Time_Now,
                 Valid => Time_Valid);
      if not Time_Valid then
        -- Can't extrapolate
         Position := Cartesian.Zero_Position;
      else
         -- How many seconds change
         T_Delta := Clock_Utils.Delta_Time(Last_Time,Time_Now);
         Extrapolate_Dimension(Last_Position.X,
                               Last_Velocity.vX,
                               Position.X);
         Extrapolate_Dimension(Last_Position.Y,
                               Last_Velocity.vY,
                               Position.Y);
         Extrapolate_Dimension(Last_Position.Z,
                               Last_Velocity.vZ,
                               Position.Z);
      end if;
   end Extrapolate_position;

   --------- Public subprograms

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle
     --# global in Last_Position, Last_Time, Last_Velocity;
     --#        in out BIT_State;
     --#        in out Clock.Time;
     --#        in Bus.Outputs;
     --#        in out Bus.Inputs;
     --# derives
     --#        BIT_State
     --#          from *, Bus.Outputs &
     --#        Bus.Inputs from *, Clock.Time,
     --#        Last_Position, Last_Time,
     --#        Last_Velocity, BIT_State &
     --#        Clock.Time from *;
   is
      Position : Cartesian.Position;
      Datum : Bus.Word;

      procedure Write_Distance(D : in Meter;
                               I1 : in Bus.Word_Index;
                               I2 : in Bus.Word_Index)
        --# global in out Bus.Inputs;
        --# derives Bus.Inputs from
        --#   *, D, I1, I2;
      is
      begin
         Rt1553.Write_Word(Data => Bus.Word(D / 16#10000#),
                           Idx  => I1,
                           Subaddress_Idx => 1,
                           Src => Bus_id);
         Rt1553.Write_Word(Data => Bus.Word(D mod 16#10000#),
                           Idx  => I2,
                           Subaddress_Idx => 1,
                           Src => Bus_Id);
      end Write_Distance;
   begin
      Extrapolate_Position(position);
      -- Write the X position info to T1 word 1, 2
      Write_Distance(D => Position.X,
                     I1 => 1,
                     I2 => 2);
      Write_Distance(D => Position.Y,
                     I1 => 3,
                     I2 => 4);
      Write_Distance(D => Position.Z,
                     I1 => 5,
                     I2 => 6);
      -- Write the BIT phase to T1 word 7
      Rt1553.Write_Word(Data => IBIT.Phase_Lookup(BIT_Machine.Phase(Bit_State)),
                       Idx => 7,
                       Subaddress_Idx => 1,
                       Src => Bus_id);
      -- Read the BIT info off R1
      Rt1553.Read_Word(Src => Bus_id,
                       Idx => 1,
                       Subaddress_Idx => 1,
                       Data => Datum);
      BIT_Machine.Change_State(Word => Datum,
                               State => Bit_state);
      -- And cycle the BIT
      BIT_Machine.Step(Bit_State);
   end Cycle;

   -- Set the current position
   procedure Set_Location(X, Y, Z : in Meter)
   --# global    out Last_position, last_time;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_position from x, y, z, Clock.Time &
   --#         Last_Time     from Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_Position := Cartesian.Position'(X => X, Y => Y, Z => Z);
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_position := Cartesian.Zero_Position;
      end if;
   end Set_location;

   -- Move the current position
   procedure Move(DX, DY, DZ : in Meter)
     --# global in out Last_position;
     --#         out last_time;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_position from *, dx, dy, dz, Clock.Time &
   --#         Last_Time     from Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_Position := Cartesian.Position'(X => Last_Position.X + dx,
                                           Y => Last_Position.Y + Dy,
                                           Z => Last_Position.Z + dZ);
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_position := Cartesian.Zero_Position;
      end if;
   end Move;

   -- Set the current motion
   procedure Set_velocity(vX, vY, vZ : in Meter_Per_Sec)
   --# global    out last_time, last_velocity;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_Time     from Clock.Time &
   --#         Last_velocity from vx, vy, vz, Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_Velocity := Cartesian.Velocity'(Vx => Vx, Vy => Vy, Vz => Vz);
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_velocity := Cartesian.Zero_velocity;
      end if;
   end Set_velocity;

   -- Read the current speed
   procedure Read_Location(X, Y, Z : out Meter)
     --# global in     Last_Position, Last_Time, Last_velocity;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         x, y, z from last_position, Last_Time, last_velocity,
     --#         Clock.Time;
   is
      Position : Cartesian.Position;
   begin
      Extrapolate_position(position);
      X := Position.X;
      Y := Position.Y;
      Z := Position.Z;
   end Read_Location;

   procedure Fail_Next_Bit
     --# global in out BIT_State;
     --# derives BIT_State from *;
   is begin
      BIT_Machine.Fail_Next(Bit_State);
   end Fail_Next_Bit;

   procedure Init
     --# global out Last_Position, Last_Time, Last_Velocity, BIT_State;
     --#        in out Bus.Inputs;
     --# derives Last_Position, Last_Time, last_velocity, BIT_State from &
     --#        Bus.Inputs from *;
   is begin
      -- Initialise the bus message 1T
      RT1553.Set_Message_Valid(Subaddress_Idx => 1,
                               Src => Bus_id);
      -- Initialise the variables
      Last_Position := Cartesian.Zero_position;
      Last_Time     := Clock.Millisecond'First;
      Last_Velocity := Cartesian.Zero_velocity;
      BIT_Machine.Create(Ticks_To_Complete => 25,
                         State => Bit_State);
   end Init;

   procedure Command is separate;
end Ins;
