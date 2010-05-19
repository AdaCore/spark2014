-- MCU interface to the airspeed over the bus
--
-- $Log: if_airspeed.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/10 20:06:25  adi
-- Added IBIT phase detection
--
-- Revision 1.1  2003/08/10 16:46:11  adi
-- Initial revision
--
--
--
with SystemTypes, MeasureTypes, Ibit;
use type MeasureTypes.Meter_Per_sec;
--# inherit SystemTypes, MeasureTypes, Bus, Ibit,
--# bc1553;
package If_Airspeed
  --# own State;
  --# initializes State;
is
   -- Find out the current IBIT phase
   function Get_Ibit_State return Ibit.Phase;
   --# global state;

   -- Find out the current speed and its validity
   procedure Get_Speed(Speed : out MeasureTypes.Meter_Per_sec;
                        Valid  : out Boolean);
   --# global in State;
   --# derives Speed, Valid from State;

   -- Kick off a airspeed IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a airspeed IBIT
   procedure Ibit_Stop;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Poll the bus
   procedure Poll;
   --# global in out State;
   --#        in Bus.Inputs;
   --# derives State from *, Bus.Inputs;

   -- Initialise
   procedure Init;
   --# global out State;
   --#        in out Bus.Outputs;
   --# derives State from &
   --#         Bus.Outputs from *;

   -- test point
   procedure Command;
   --# derives;
end If_Airspeed;
