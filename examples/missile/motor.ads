-- Motor simulator
--
-- $Log: motor.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/01 18:18:19  adi
-- Fixed for implementation
--
-- Revision 1.1  2003/08/31 21:11:26  adi
-- Initial revision
--
--
with MeasureTypes,Clock,motor_cfg;
use type Clock.Millisecond, motor_Cfg.Motor_power;
--# inherit state_types, MeasureTypes, Bus, Rt1553,
--#         Clock, Clock_Utils, motor_cfg,
--#         IBIT, Bit_Machine, systemtypes,
--#         measuretypes.encode, measuretypes.decode;
package Motor
  --# own State;
  --# initializes State;
is
   subtype Power is Motor_Cfg.Motor_Power;

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle;
   --# global in out State;
   --#        in out Clock.Time;
   --#        in Bus.Outputs;
   --#        in out Bus.Inputs;
   --# derives State from *, Bus.Outputs, clock.time &
   --#        Bus.Inputs from *, Clock.Time, State &
   --#        Clock.Time from *, state, bus.outputs;

   -- Set the current thrust level
   procedure Set_thrust(New_Level : in Power);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, new_level;

   -- Read the current thrust levle
   procedure Read_thrust(This_Level : out Power);
   --# global in     State;
   --#         in out clock.time;
   --# derives
   --#    this_level from
   --#         State, clock.time &
   --#    clock.time from *;

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
end Motor;
