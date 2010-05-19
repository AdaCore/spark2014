-- MCU interface to the compass over the bus
--
-- $Log: if_compass.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/09/10 20:18:22  adi
-- Added get_ibit_state
--
-- Revision 1.2  2003/08/08 20:31:28  adi
-- Use Angle_Ops public child
--
-- Revision 1.1  2003/08/02 19:49:15  adi
-- Initial revision
--
--
with SystemTypes, MeasureTypes, Ibit;
use type MeasureTypes.Millirad;
--# inherit SystemTypes, MeasureTypes, Bus, Ibit,
--# bc1553, Measuretypes.angle_ops;
package If_Compass
  --# own State;
  --# initializes State;
is
   -- Get IBIT state
   function Get_IBIT_State return Ibit.Phase;
   --# global state;

   -- Find out the current angle in the XY plane off magnetic north
   procedure Get_XY(Angle : out MeasureTypes.Millirad;
                    Valid  : out Boolean);
   --# global in State;
   --# derives Angle, Valid from State;

   -- Find out the current angle in the YZ plane off Earth tangent plane
   procedure Get_YZ(Angle : out MeasureTypes.Millirad;
                    Valid  : out Boolean);
   --# global in State;
   --# derives Angle, Valid from State;

   -- Kick off a component IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a component IBIT
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
end If_Compass;
