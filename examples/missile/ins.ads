-- INS simulator
--
-- $Log: ins.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/10 17:13:53  adi
-- Added cartesian use
--
-- Revision 1.1  2003/08/10 17:06:23  adi
-- Initial revision
--
--
--
with MeasureTypes,Clock,Cartesian;
use type MeasureTypes.Meter;
use type MeasureTypes.Meter_Per_Sec;
use type Clock.Millisecond;
--# inherit MeasureTypes, Bus, Rt1553,
--#         Clock, Clock_Utils, SystemTypes,
--#         IBIT, Bit_Machine, Cartesian;
package Ins
  --# own State;
  --# initializes State;
is
   -- Type renamings for brevity
   subtype Meter is Measuretypes.Meter;
   subtype Meter_Per_Sec is MeasureTypes.Meter_Per_Sec;

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

   -- Set the current x, y and Z differential
   procedure Set_Location(x : in Meter;
                          y : in Meter;
                          Z : in Meter);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, x,y,z;

   -- Set the current motion
   procedure Set_Velocity(vx : in Meter_Per_sec;
                          vy : in Meter_Per_sec;
                          vZ : in Meter_Per_Sec);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, vx,vy,vz;

   -- Change the current location by a certain amount
   procedure Move(Dx : in Meter;
                  Dy : in Meter;
                  Dz : in Meter);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, dx,dy,dz;

   -- Read the current location
   procedure Read_Location(X : out Meter;
                           Y : out Meter;
                           Z : out Meter);
   --# global in     State;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         X,Y,Z from State, Clock.Time;

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
end Ins;

