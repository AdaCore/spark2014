-- RADAR simulator
--
-- $Log: radar.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.6  2003/08/25 13:29:19  adi
-- Use measuretypes.encode
--
-- Revision 1.5  2003/08/24 18:44:58  adi
-- Amended cycle anno
--
-- Revision 1.4  2003/08/23 13:42:53  adi
-- Added state_types
--
-- Revision 1.3  2003/08/22 18:21:37  adi
-- Changed accessing to 2-d not 1-d
--
-- Revision 1.2  2003/08/20 21:14:59  adi
-- Corrected use of clock.time
--
-- Revision 1.1  2003/08/18 19:49:33  adi
-- Initial revision
--
--
with MeasureTypes,Clock,Radar_Cfg,random;
use type MeasureTypes.Meter;
use type MeasureTypes.Meter_Per_Sec;
use type Clock.Millisecond;
use type Radar_Cfg.Sector_Range;
use type Random.Value;
--# inherit MeasureTypes, measuretypes.encode,
--#         Bus, Rt1553,
--#         Clock, Clock_Utils,
--#         random, SystemTypes, state_types,
--#         IBIT, Bit_Machine, radar_cfg;
package Radar
  --# own State;
  --# initializes State;
is
   -- Type renamings for brevity
   subtype Meter is Measuretypes.Meter;
   subtype Meter_Per_Sec is MeasureTypes.Meter_Per_Sec;
   subtype Sector is Radar_Cfg.Sector_Range;

   -- Cone of detection is 800 millirads left and right of axis
   -- Detection distance up to 10,000m
   -- Accuracy is +- 20millirads
   -- Also detects velocity relative to missile long axis

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle;
   --# global in out State;
   --#        in Bus.Outputs;
   --#        in out Bus.Inputs;
   --# derives State from *, Bus.Outputs &
   --#        Bus.Inputs from *, State, bus.outputs;


   procedure Set_Bearing_Return(Sx, Sy : in Sector;
                                D : in Meter;
                                V : in Meter_Per_sec);
   --# global in out State;
   --# derives State from *, Sx, Sy, D, V;

   -- Read what's at a bearing
   procedure Read_Location(Sx, Sy : in Sector;
                           D : out Meter;
                           V : out Meter_Per_sec);
   --# global in     State;
   --# derives D, V from State, Sx, Sy;

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

end Radar;

