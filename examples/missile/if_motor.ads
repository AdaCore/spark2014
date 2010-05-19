-- MCU interface to the motor over the bus
--
-- $Log: if_motor.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/11 19:50:55  adi
-- Added get_ibit_state
--
-- Revision 1.1  2003/09/01 18:26:22  adi
-- Initial revision
--
--
with motor_cfg, Ibit;
--# inherit SystemTypes, MeasureTypes, Bus, Ibit,
--# bc1553, motor_cfg, measuretypes.encode, measuretypes.decode;
package If_Motor
  --# own State;
  --# initializes State;
is
   subtype Power is Motor_Cfg.Motor_Power;

   function Get_Ibit_State return Ibit.Phase;
   --# global state;

   -- Find out the current thrust
   procedure Get_Thrust(This_Level : out Power;
                        Valid      : out Boolean);
   --# global in State;
   --# derives this_level from State &
   --#   valid from State;

   -- Command a motor thrust level
   procedure Set_Thrust(New_Level : in Power);
   --# global in out Bus.Outputs;
   --# derives Bus.Outputs from *, new_level;

   -- Kick off a motor IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a motor IBIT
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
end If_Motor;
