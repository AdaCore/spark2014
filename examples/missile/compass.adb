-- Compass simulator implementation
--
-- $Log: compass.adb,v $
-- Revision 1.3  2004/12/17 17:51:22  adi
-- Fixed compass angle conversions and checks so that compass.in passes
--
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/08/08 20:29:48  adi
-- Use Angle_Ops public child
--
-- Revision 1.2  2003/08/06 20:37:31  adi
-- use separate bit_machine package
--
-- Revision 1.1  2003/08/04 20:57:38  adi
-- Initial revision
--
--
--
--with ada.text_io;

with Clock_Utils,SystemTypes,Measuretypes.Angle_ops;
with Bus,RT1553,IBIT,Bit_Machine;
package body Compass
  --# own State is
  --#     Last_XY, Last_YZ,
  --#     Last_Time,
  --#     Last_dXY, Last_dYZ,
  --#     BIT_State;
is

   Last_XY,
   Last_YZ   : Measuretypes.Millirad := Measuretypes.Angle_zero;
   Last_Time : Clock.Millisecond := Clock.Millisecond'First;
   Last_DXY,
   Last_dYZ  : Measuretypes.Millirad_Per_Sec := 0;
   Bit_State : Bit_Machine.Machine := Bit_Machine.Initial_Machine;

   -- Can't extrapolate angles past 10 minutes
   Max_Extrapolate_Time : constant Clock.Millisecond := 600_000;

   -- Work out the current XY or YZ angle.
   procedure Extrapolate_Angle(Last_Angle : in Measuretypes.Millirad;
                               Last_Delta : in Measuretypes.Millirad_Per_Sec;
                               New_Angle : out Measuretypes.Millirad)
     --# global in     Last_Time;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         New_Angle from Clock.Time, Last_Angle,
     --#         Last_Delta, Last_Time;
   is
      Time_Now,T_Delta : Clock.Millisecond;
      Time_Valid : Boolean;
      Delta_Thousand_Millirads : Systemtypes.Integer32;
      Delta_Angle : Measuretypes.Millirad;
   begin
      Clock.Read(T => Time_Now,
                 Valid => Time_Valid);
      if not Time_Valid then
        -- Can't extrapolate
        New_Angle := Measuretypes.Angle_zero;
      else
         -- How many seconds change
         T_Delta := Clock_Utils.Delta_Time(Last_Time,Time_Now);
         if T_Delta = 0 then
            --Ada.Text_Io.Put_Line("Time not valid");
            -- No time change; new is same as old
            New_Angle := Last_Angle;
         elsif T_Delta > Max_Extrapolate_Time then
            --Ada.Text_Io.Put_Line("Too great a time since last reading");
            New_Angle := Last_Angle;
         else
            -- Need to extrapolate angle swept in T_Delta milliseconds
            --  at Last_Delta millirads per sec == (Last_Delta / 1000) millirads per millisec
            Delta_Thousand_Millirads :=
               Systemtypes.Integer32(Last_Delta) * Systemtypes.Integer32(T_Delta);
            -- Reduce delta_thousand_millirads to a real millirads,
            -- dividing by 1000 to represent conversion from millirads/millisec to millirads/sec
            Delta_Angle := Measuretypes.Angle_Ops.Int_To_Millirad(Delta_Thousand_Millirads / 1000);
            -- Now work out the new angle
            New_Angle := Measuretypes.Angle_Ops.Sum(Last_Angle,Delta_Angle);
         end if;
      End if;
      -- Useful for debugging:
      --ada.text_io.put_line("Extrapolating angle " &
      --                     Measuretypes.io.millirad(Last_Angle) &
      --                     " with delta " &
      --                     Measuretypes.millirad_per_sec'image(Last_Delta) &
      --                     "mR/s over " &
      --                     Clock.Millisecond'Image(T_Delta) &
      --                     "ms to " &
      --                     Measuretypes.io.millirad(New_Angle));
   end Extrapolate_angle;

   --------- Public subprograms

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle
     --# global in Last_XY, Last_YZ, Last_Time, Last_dXY, Last_dYZ;
     --#        in out BIT_State;
     --#        in out Clock.Time;
     --#        in Bus.Outputs;
     --#        in out Bus.Inputs;
     --# derives
     --#        BIT_State
     --#          from *, Bus.Outputs &
     --#        Bus.Inputs from *, Clock.Time, Last_XY, Last_YZ, Last_Time,
     --#        Last_dXY, Last_dYZ, BIT_State &
     --#        Clock.Time from *;
   is
      This_Angle : Measuretypes.millirad;
      Datum : Bus.Word;
   begin
      -- Do it for XY angle
      Extrapolate_Angle(Last_Angle => Last_XY,
                        Last_Delta => Last_DXY,
                        New_Angle => This_Angle);
      Datum := Measuretypes.Angle_Ops.Millirad_To_Word(This_Angle);
      -- Write the XY info to T1 word 1
      Rt1553.Write_Word(Data => datum,
                        Idx  => 1,
                        Subaddress_Idx => 1,
                        Src => RT1553.Compass);
      -- Do it for YZ angle
      Extrapolate_Angle(Last_Angle => Last_YZ,
                        Last_Delta => Last_DYZ,
                        New_Angle => This_Angle);
      Datum := Measuretypes.Angle_Ops.Millirad_To_Word(This_Angle);
      -- Write the XY info to T1 word 2
      Rt1553.Write_Word(Data => datum,
                        Idx  => 2,
                        Subaddress_Idx => 1,
                        Src => RT1553.Compass);

      -- Write the BIT phase to T1 word 3
      Rt1553.Write_Word(Data => IBIT.Phase_Lookup(BIT_Machine.Phase(Bit_State)),
                       Idx => 3,
                       Subaddress_Idx => 1,
                       Src => RT1553.Compass);
      -- Read the BIT info off R1
      Rt1553.Read_Word(Src => Rt1553.Compass,
                       Idx => 1,
                       Subaddress_Idx => 1,
                       Data => Datum);
      BIT_machine.Change_State(Word => Datum,
                               State => Bit_State);
      -- And cycle the BIT
      BIT_Machine.Step(Bit_State);
   end Cycle;

   -- Set the current XY angle
   procedure Set_XY(XY : in Angle_Degrees)
   --# global    out Last_XY, Last_Time;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_XY from XY, clock.time &
   --#         Last_Time     from Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_XY := Measuretypes.Angle_Ops.Degree_To_Millirad(XY);
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_XY := Measuretypes.Angle_Zero;
      end if;
   end Set_XY;

   -- Set the current YZ angle
   procedure Set_YZ(YZ : in Angle_Degrees)
   --# global    out Last_YZ, Last_Time;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_YZ from YZ, clock.time &
   --#         Last_Time     from Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_YZ := Measuretypes.Angle_Ops.Degree_To_Millirad(YZ);
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_YZ := Measuretypes.Angle_Zero;
      end if;
   end Set_YZ;

   -- Set the current XY delta
   procedure Set_dXY(dXY : in Measuretypes.Millirad_Per_Sec)
   --# global    out Last_dXY, Last_Time;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_dXY from dXY, clock.time &
   --#         Last_Time     from Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_dXY := dXY;
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_dXY := 0;
      end if;
   end Set_dXY;

   -- Set the current YZ delta
   procedure Set_dYZ(dYZ : in Measuretypes.Millirad_Per_Sec)
   --# global    out Last_dYZ, Last_Time;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Last_dYZ from dYZ, clock.time &
   --#         Last_Time     from Clock.Time;
   is
      Time_Valid : Boolean;
   begin
      Last_dYZ := dYZ;
      Clock.Read(Last_Time,Time_Valid);
      if not Time_Valid then
         Last_dYZ := 0;
      end if;
   end Set_dYZ;

   -- Read the current XY angle
   procedure Read_XY(XY : out Angle_Degrees)
     --# global in     Last_XY, Last_Time, Last_dXY;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         XY from Last_XY, Last_Time, Last_dXY,
     --#         Clock.Time;
   is
      Xy_Millirad : Measuretypes.Millirad;
   begin
      Extrapolate_angle(Last_Angle => Last_XY,
                        Last_Delta => Last_DXY,
                        New_Angle => Xy_millirad);
      Xy := Measuretypes.Angle_Ops.Round_Degree(Xy_Millirad);
   end Read_XY;

   -- Read the current XY delta
   procedure Read_dXY(Delta_angle : out Measuretypes.Millirad_Per_Sec)
     --# global in     Last_dXY;
     --# derives Delta_angle from last_dXY;
   is
   begin
      Delta_Angle := Last_Dxy;
   end Read_dXY;

   -- Read the current YZ angle
   procedure Read_YZ(YZ : out Angle_Degrees)
     --# global in     Last_YZ, Last_Time, Last_dYZ;
     --#        in out Clock.Time;
     --# derives Clock.Time from * &
     --#         YZ from Last_YZ, Last_Time, Last_dYZ,
     --#         Clock.Time;
   is
      YZ_Millirad : Measuretypes.Millirad;
   begin
      Extrapolate_angle(Last_Angle => Last_YZ,
                        Last_Delta => Last_DYZ,
                        New_Angle  => YZ_millirad);
      YZ := Measuretypes.Angle_Ops.Round_Degree(YZ_Millirad);
   end Read_YZ;

   -- Read the current YZ delta
   procedure Read_dYZ(Delta_angle : out Measuretypes.Millirad_Per_Sec)
     --# global in     Last_dYZ;
     --# derives Delta_angle from last_dYZ;
   is
   begin
      Delta_Angle := Last_dYZ;
   end Read_dYZ;

   procedure Fail_Next_Bit
     --# global in out BIT_State;
     --# derives BIT_State from *;
   is begin
      BIT_Machine.Fail_Next(Bit_State);
   end Fail_Next_Bit;

   procedure Init
     --# global out Last_XY, Last_YZ, Last_Time,
     --#        Last_dXY, Last_dYZ, BIT_State;
     --#        in out Bus.Inputs;
     --# derives Last_XY, Last_YZ, Last_Time,
     --#        Last_dXY, Last_dYZ, BIT_State from &
     --#        Bus.Inputs from *;
   is begin
      -- Initialise the bus message 1T
      RT1553.Set_Message_Valid(Subaddress_Idx => 1,
                               Src => RT1553.Compass);
      -- Initialise the variables
      Last_XY := Measuretypes.Angle_zero;
      Last_YZ := Measuretypes.Angle_zero;
      Last_Time     := Clock.Millisecond'First;
      Last_DXY := 0;
      Last_DYZ := 0;
      BIT_Machine.Create(Ticks_To_Complete => 15,
                         State => Bit_State);
   end Init;

   procedure Command is separate;
end Compass;
