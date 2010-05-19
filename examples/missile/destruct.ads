-- Self-destruct simulator
--
-- $Log: destruct.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 19:14:29  adi
-- Initial revision
--
--
with Clock,Destruct_cfg;
use type Clock.Millisecond, Destruct_Cfg.state;
--# inherit state_types, Bus, Rt1553,
--#         Clock, Clock_Utils, destruct_cfg,
--#         IBIT, Bit_Machine, systemtypes;
package Destruct
  --# own State;
  --# initializes State;
is
   subtype Stage is Destruct_Cfg.State;

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

   -- Set the current code exchange stage level
   procedure Set_Stage(New_Stage : in Stage);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, New_Stage;

   -- Read the current exchange stage
   procedure Read_Stage(This_Stage : out Stage);
   --# global in     State;
   --# derives
   --#    this_stage from state;

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
end Destruct;
