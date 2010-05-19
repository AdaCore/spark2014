-- MCU interface to the fuze over the bus
--
-- $Log: if_fuze.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.5  2003/09/10 21:01:16  adi
-- Added get_ibit_state
--
-- Revision 1.4  2003/08/17 15:29:52  adi
-- Fixed Poll to write out too
--
-- Revision 1.3  2003/08/17 15:11:26  adi
-- Added a use type and corrected annos
--
-- Revision 1.2  2003/08/17 15:01:50  adi
-- Corrected arm/disarm annotations
--
-- Revision 1.1  2003/08/17 14:39:49  adi
-- Initial revision
--
--
with SystemTypes,
  MeasureTypes,
  Ibit, State_Types;
use type State_Types.Fuze;
--# inherit SystemTypes, MeasureTypes, Bus, Ibit,
--# bc1553,state_types;
package If_Fuze
  --# own State;
  --# initializes State;
is
   function Get_Ibit_State return Ibit.Phase;
   --# global state;

   -- Find out the current state
   procedure Get_State(Action_State : out State_Types.Fuze;
                       Valid  : out Boolean);
   --# global in State;
   --# derives action_state, Valid from State;

   -- Command a fuzing change
   procedure Arm;
   --# global in out Bus.Outputs; in state;
   --# derives Bus.Outputs from *, state;

   procedure Disarm;
   --# global in out Bus.Outputs;
   --# derives Bus.Outputs from *;

   -- Kick off a fuze IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a fuze IBIT
   procedure Ibit_Stop;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Poll the bus
   procedure Poll;
   --# global in out State;
   --#        in Bus.Inputs;
   --#        in out bus.outputs;
   --# derives State from *, Bus.Inputs &
   --#    bus.outputs from *, state, bus.inputs;

   -- Initialise
   procedure Init;
   --# global out State;
   --#        in out Bus.Outputs;
   --# derives State from &
   --#         Bus.Outputs from *;

   -- test point
   procedure Command;
   --# derives;
end If_Fuze;
