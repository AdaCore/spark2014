-- MCU interface to the fins over the bus
--
-- $Log: if_steer.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/09/11 19:54:16  adi
-- Added get_ibit_state
--
-- Revision 1.2  2003/08/31 20:28:51  adi
-- Updated annos for implementation
--
-- Revision 1.1  2003/08/31 20:15:48  adi
-- Initial revision
--
--
with Steer_cfg, Ibit;
use type Steer_Cfg.Fin_Angle, Steer_Cfg.fin;
--# inherit SystemTypes, MeasureTypes, Bus, Ibit,
--# bc1553,steer_cfg, steer_cfg.encode, steer_cfg.decode;
package If_Steer
  --# own State;
  --# initializes State;
is
   subtype Fin is Steer_Cfg.Fin;
   Subtype Angle is Steer_Cfg.Fin_Angle;

   function Get_Ibit_State return Ibit.Phase;
   --# global state;

   -- Find out the current deflection
   procedure Get_Deflection(For_Fin    : in Fin;
                            This_Angle : out Angle;
                            Valid      : out Boolean);
   --# global in State;
   --# derives this_angle from State, for_fin &
   --#   valid from state;

   -- Command a fin steering deflection
   procedure Set_Deflection(For_Fin : in Fin;
                            New_Angle : in Angle);
   --# global in out Bus.Outputs;
   --# derives Bus.Outputs from *, for_fin, new_angle;

   -- Kick off a steer IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a steer IBIT
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
end If_Steer;
