-- Fuel simulator
--
-- $Log: fuel.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/17 11:57:14  adi
-- Derived from ins
--
-- Revision 1.1  2003/08/12 18:30:03  adi
-- Initial revision
--
--
with MeasureTypes,Clock;
use type MeasureTypes.Kilo;
use type Measuretypes.Gram_Per_Sec;
use type Clock.Millisecond;
--# inherit MeasureTypes, Bus, Rt1553,
--#         Clock, Clock_Utils, SystemTypes,
--#         IBIT, Bit_Machine;
package Fuel
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

   -- Set the current fuel level
   procedure Set_Level(level : in Measuretypes.Kilo);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, level;

   -- Set the current burn rate
   procedure Set_Rate(Rate : in Measuretypes.Gram_Per_Sec);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, rate;

   -- Read the current level
   procedure Read_Level(level : out Measuretypes.Kilo);
   --# global in     State;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         level from State, Clock.Time;

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
end Fuel;
