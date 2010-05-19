-- MCU interface to the radar over the bus
--
-- $Log: if_radar.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.4  2003/09/11 19:52:07  adi
-- Added get_ibit_state
--
-- Revision 1.3  2003/08/25 19:45:04  adi
-- Updated annos
--
-- Revision 1.2  2003/08/25 14:43:09  adi
-- Added use of measuretypes.decode
--
-- Revision 1.1  2003/08/25 14:13:00  adi
-- Initial revision
--
--
with SystemTypes,
  MeasureTypes,
  Radar_Cfg,
  Ibit;
--# inherit SystemTypes, MeasureTypes, Bus, Ibit,
--# bc1553, radar_cfg, state_types, measuretypes.decode;
package If_Radar
  --# own State;
  --# initializes State;
is
   function Get_Ibit_State return Ibit.Phase;
   --# global state;

   -- Ping the radar
   procedure Ping(Sx, Sy : in Radar_Cfg.Sector_Range);
   --# global in out Bus.Outputs, state;
   --# derives Bus.Outputs from *, sx, sy &
   --#         state from *, sx, sy;

   -- Sweep the radar
   procedure Sweep(Sx_Start, Sx_End : in Radar_Cfg.Sector_Range;
                   Sy_Start, Sy_End : in Radar_Cfg.Sector_Range);
   --# global in out bus.outputs, state;
   --# derives bus.outputs from *, sx_start, sx_end,
   --#          sy_start, sy_end &
   --#         state from *, sx_start, sx_end, sy_start, sy_end;

   procedure Read_Ping(Sx,Sy : out Radar_Cfg.Sector_Range;
                       Dist  : out Measuretypes.Meter;
                       Vel   : out Measuretypes.Meter_Per_Sec);
   --# global in state;
   --# derives sx, sy, dist, vel from state;

   procedure Read_sweep(Sx_start,Sx_end : out Radar_Cfg.Sector_Range;
                        Sy_Start,Sy_End : out Radar_Cfg.Sector_Range;
                        Grid : out Measuretypes.Bit4_Array);
   --# global in state;
   --# derives sx_start, sx_end, sy_start, sy_end,
   --#         grid from state;

   -- Kick off a radar IBIT
   procedure Ibit_Start;
   --# global in out Bus.Outputs, State;
   --# derives Bus.Outputs from * &
   --#         State from *;

   -- Stop a radar IBIT
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
end If_Radar;
