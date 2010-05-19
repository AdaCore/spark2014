-- IR simulator
--
-- $Log: ir.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/27 20:46:05  adi
-- Initial revision
--
--
with MeasureTypes,Ir_Cfg,random;
use type MeasureTypes.Meter;
use type Measuretypes.Kelvin;
use type Ir_Cfg.Sector_Range;
use type Random.Value;
--# inherit MeasureTypes, measuretypes.encode,
--#         Bus, Rt1553,
--#         random, SystemTypes, state_types,
--#         IBIT, Bit_Machine, ir_cfg;
package IR
  --# own State;
  --# initializes State;
is
   -- Type renamings for brevity
   subtype Meter is Measuretypes.Meter;
   subtype Kelvin is Measuretypes.Kelvin;
   subtype Sector is Ir_Cfg.Sector_Range;

   -- Cone of detection is 1200 millirads left and right of axis
   -- Detection distance up to 30,000m
   -- Accuracy is +- 100millirads
   -- Also detects range via expected temperature, +/- 30%

   -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle;
   --# global in out State;
   --#        in Bus.Outputs;
   --#        in out Bus.Inputs;
   --# derives State from *, Bus.Outputs &
   --#        Bus.Inputs from *, State, bus.outputs;


   procedure Set_cell_Return(Sx, Sy : in Sector;
                                T : in Kelvin);
   --# global in out State;
   --# derives State from *, Sx, Sy, T;

   -- Read what's at a cell
   procedure Read_Location(Sx, Sy : in Sector;
                           T : out Kelvin);
   --# global in     State;
   --# derives T from State, Sx, Sy;

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

end Ir;
