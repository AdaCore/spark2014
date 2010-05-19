-- MCU interface to the IR over the bus
--
-- $Log: if_ir.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/11 19:48:12  adi
-- Added get_ibit_state
--
-- Revision 1.1  2003/08/27 20:54:50  adi
-- Initial revision
--
--
with SystemTypes,
  MeasureTypes,
  Ir_Cfg,
  Ibit;
--# inherit SystemTypes, MeasureTypes, Bus, Ibit,
--# bc1553, Ir_cfg, state_types, measuretypes.decode;
package If_Ir
  --# own State;
  --# initializes State;
is
   function Get_Ibit_State return Ibit.Phase;
   --# global state;

   -- Stare at an IR cell
   procedure stare(Sx, Sy : in Ir_Cfg.Sector_Range);
   --# global in out Bus.Outputs, state;
   --# derives Bus.Outputs from *, sx, sy &
   --#         state from *, sx, sy;

   -- Sweep the ir
   procedure Sweep(Sx_Start, Sx_End : in Ir_Cfg.Sector_Range;
                   Sy_Start, Sy_End : in Ir_Cfg.Sector_Range);
   --# global in out bus.outputs, state;
   --# derives bus.outputs from *, sx_start, sx_end,
   --#          sy_start, sy_end &
   --#         state from *, sx_start, sx_end, sy_start, sy_end;

   procedure Read_stare(Sx,Sy : out Ir_Cfg.Sector_Range;
                        Temp : out Measuretypes.Kelvin);
   --# global in state;
   --# derives sx, sy, temp from state;

   procedure Read_sweep(Sx_start,Sx_end : out Ir_Cfg.Sector_Range;
                        Sy_Start,Sy_End : out Ir_Cfg.Sector_Range;
                        Grid : out Measuretypes.Bit4_Array);
   --# global in state;
   --# derives sx_start, sx_end, sy_start, sy_end,
   --#         grid from state;

   -- Kick off a ir IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a ir IBIT
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
end If_Ir;
