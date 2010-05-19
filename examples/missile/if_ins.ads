-- MCU interface to the INS over the bus
--
-- $Log: if_ins.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/10 21:05:04  adi
-- Added get_ibit_state
--
-- Revision 1.1  2003/08/10 22:06:47  adi
-- Initial revision
--
--
with SystemTypes,
  MeasureTypes,
  Ibit,
  Cartesian;
use type MeasureTypes.Meter_Per_sec;
use type Measuretypes.Meter;
--# inherit SystemTypes, MeasureTypes, Bus, Ibit,
--# bc1553, cartesian;
package If_Ins
  --# own State;
  --# initializes State;
is
   function Get_Ibit_State return Ibit.Phase;
   --# global state;

   -- Find out the current location and its validity
   procedure Get_Location(Position : out Cartesian.position;
                        Valid  : out Boolean);
   --# global in State;
   --# derives position, Valid from State;

   -- Kick off a ins IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a ins IBIT
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
end If_Ins;
