-- MCU interface to the fuel over the bus
--
-- $Log: if_fuel.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/10 20:59:31  adi
-- Added get_ibit_state
--
-- Revision 1.1  2003/08/17 12:44:08  adi
-- Initial revision
--
--
with SystemTypes,
  MeasureTypes,
  Ibit;
use type MeasureTypes.Gram_Per_sec;
use type Measuretypes.kilo;
--# inherit SystemTypes, MeasureTypes, Bus, Ibit,
--# bc1553;
package If_Fuel
  --# own State;
  --# initializes State;
is
   function Get_IBIT_State return Ibit.Phase;
     --# global state;

   -- Find out the current location and its validity
   procedure Get_Level(level : out Measuretypes.kilo;
                       Valid  : out Boolean);
   --# global in State;
   --# derives level, Valid from State;

   -- Kick off a fuel IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a fuel IBIT
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
end If_Fuel;
