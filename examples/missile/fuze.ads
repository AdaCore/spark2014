-- Proximity Fuze simulator
--
-- $Log: fuze.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/08/17 14:58:25  adi
-- Updated to read back info from bus
--
-- Revision 1.2  2003/08/17 14:16:50  adi
-- Corrected actual annos
--
-- Revision 1.1  2003/08/17 13:38:22  adi
-- Initial revision
--
--
with MeasureTypes,Clock,State_types;
use type Clock.Millisecond, State_Types.fuze;
--# inherit state_types, MeasureTypes, Bus, Rt1553,
--#         Clock, Clock_Utils, SystemTypes,
--#         IBIT, Bit_Machine;
package Fuze
  --# own State;
  --# initializes State;
is
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

   -- Set the current fuze state
   procedure Set_state(New_State : in State_Types.fuze);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, new_state;

   -- Set the current fuze timer
   procedure Set_Timer(Ms : in Clock.Millisecond);
   --# global in out state;
   --# derives state from *, ms;

   -- Read the current fuze state
   procedure Read_state(This_State : out State_Types.Fuze);
   --# global in     State;
   --# derives this_state from State;

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
end Fuze;
