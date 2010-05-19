-- MCU interface to the barometer over the bus
--
-- $Log: if_barometer.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.4  2003/09/10 20:08:36  adi
-- Added IBIT state accessor
--
-- Revision 1.3  2003/02/19 19:11:57  adi
-- Added Command stub
--
-- Revision 1.2  2003/02/12 23:22:54  adi
-- Added Init procedure
--
-- Revision 1.1  2003/02/11 20:37:13  adi
-- Initial revision
--
--
with SystemTypes, MeasureTypes, Ibit;
use type MeasureTypes.Meter;
--# inherit SystemTypes, MeasureTypes, Bus, Ibit,
--# bc1553;
package If_Barometer
  --# own State;
  --# initializes State;
is
   -- Get the IBIT state
   function Get_IBIT_State return IBIT.Phase;
   --# global State;

   -- Find out the current height and its validity
   procedure Get_Height(Height : out MeasureTypes.Meter;
                        Valid  : out Boolean);
   --# global in State;
   --# derives Height, Valid from State;

   -- Kick off a barometer IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a barometer IBIT
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
end If_Barometer;
