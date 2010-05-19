-- Compass simulator
--
-- $Log: compass.ads,v $
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
-- Revision 1.4  2003/08/08 20:29:29  adi
-- Use Angle_Ops public child
--
-- Revision 1.3  2003/08/06 20:37:54  adi
-- Use Bit_Machine
--
-- Revision 1.2  2003/08/05 18:39:22  adi
-- Added read_dxy, read_dyz
--
-- Revision 1.1  2003/08/03 12:47:10  adi
-- Initial revision
--
--
--
with MeasureTypes,Clock,Systemtypes;
use type MeasureTypes.Millirad;
use type Clock.Millisecond;
--# inherit MeasureTypes, Bus, Rt1553,
--#         Clock, Clock_Utils, SystemTypes,
--#         IBIT, Bit_Machine, measuretypes.angle_ops;
package Compass
  --# own State;
  --# initializes State;
is
   -- Type renamings for brevity
   subtype Angle_Degrees is Measuretypes.Angle_Degrees;

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle;
   --# global in out State;
   --#        in out Clock.Time;
   --#        in Bus.Outputs;
   --#        in out Bus.Inputs;
   --# derives State from *, Bus.Outputs &
   --#        Bus.Inputs from *, Clock.Time, State &
   --#        Clock.Time from *;

   -- Set the current XY angle
   procedure Set_XY(XY : in Angle_Degrees);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, XY;

   -- Set the current XY angle rate of change
   procedure Set_dXY(dXY : in Measuretypes.Millirad_Per_Sec);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, dXY;

   -- Read the current XY angle
   procedure Read_XY(XY : out Angle_Degrees);
   --# global in     State;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         XY from State, Clock.Time;

   -- Read the current XY delta
   procedure Read_dXY(Delta_angle : out Measuretypes.Millirad_Per_Sec);
   --# global in     State;
   --# derives Delta_angle from State;

   -- Set the current YZ angle
   procedure Set_YZ(YZ : in Angle_Degrees);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, YZ;

   -- Set the current YZ angle rate of change
   procedure Set_dYZ(dYZ : in Measuretypes.Millirad_Per_Sec);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, dYZ;

   -- Read the current YZ angle
   procedure Read_YZ(YZ : out Angle_Degrees);
   --# global in     State;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         YZ from State, Clock.Time;

   -- Read the current YZ delta
   procedure Read_dYZ(Delta_angle : out Measuretypes.Millirad_Per_Sec);
   --# global in     State;
   --# derives Delta_angle from State;

   -- Cause the next BIT to fail
   procedure Fail_Next_Bit;
   --# global in out State;
   --# derives State from *;

   procedure Init;
   --# global out State;
   --#        in out Bus.Inputs;
   --# derives State from &
   --#         Bus.Inputs from *;

   -- Test stub
   procedure Command;
   --# derives;
end Compass;
