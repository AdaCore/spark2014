-- MCU interface to the warhead over the bus
--
-- $Log: if_warhead.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/11 19:57:01  adi
-- Added get_ibit_state
--
-- Revision 1.1  2003/09/01 18:26:31  adi
-- Initial revision
--
--
with SystemTypes,Ibit, Warhead_Cfg;
--# inherit SystemTypes, Bus, Ibit, bc1553, warhead_cfg;
package If_Warhead
  --# own State;
  --# initializes State;
is
   subtype Stage is Warhead_Cfg.State;

   function Get_Ibit_State return Ibit.Phase;
   --# global state;

   -- Find out the current state
   procedure Get_Stage(Action_Stage : out Stage;
                       Valid  : out Boolean);
   --# global in State;
   --# derives action_stage, Valid from State;

   -- Command a new stage
   procedure Set_Stage(New_Stage : in Stage);
   --# global in out Bus.Outputs;
   --# derives Bus.Outputs from *, new_stage;

   -- Kick off a warhead IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a warhead IBIT
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
end If_Warhead;
