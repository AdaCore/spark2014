-- MCU interface to the radar, implementation
--
-- $Log: if_radar.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/09/11 19:52:47  adi
-- Added get_ibit_state
--
-- Revision 1.2  2003/08/25 20:31:57  adi
-- Corrected feedback check
--
-- Revision 1.1  2003/08/25 19:44:55  adi
-- Initial revision
--
--
with Bc1553, Bus, State_Types, Measuretypes.decode;
package body If_Radar
  --# own State is
  --#     Last_ping, Last_sweep, Ibit_Request;
is
   subtype Sector is Radar_Cfg.Sector_Range;
   type Ping_Request is record
      Sx, Sy : Sector;
      Fresh_Request, Fresh_Answer : Boolean;
      Distance : Measuretypes.Meter;
      Velocity : Measuretypes.Meter_Per_Sec;
   end record;

   type Sweep_Request is record
      Sx_Start, Sx_End : Sector;
      Sy_Start, Sy_End : Sector;
      Fresh_Request, Fresh_Answer : Boolean;
      Grid : Measuretypes.Bit4_Array;
   end record;

   Null_Ping : constant Ping_Request
     := Ping_Request'(Sx => 0,
                      Sy => 0,
                      Fresh_Request => False,
                      Fresh_Answer => False,
                      Distance => 0,
                      Velocity => 0);

   Null_Sweep : constant Sweep_Request
     := Sweep_Request'(Sx_Start => 0,
                       Sx_End   => 0,
                       Sy_Start => 0,
                       Sy_End   => 0,
                       Fresh_Request => False,
                       Fresh_Answer => False,
                       Grid => Measuretypes.Bit4_Array'
                       (others => Measuretypes.Bit4_Slice'(others => False))
                       );

   Last_Ping : Ping_Request := Null_ping;
   Last_Sweep : Sweep_Request := Null_sweep;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   Bus_Id : constant Bc1553.Lru_Name := Bc1553.Radar;

   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
   end Get_Ibit_State;

   -- Ping the radar
   procedure Ping(Sx, Sy : in Radar_Cfg.Sector_Range)
   --# global in out Bus.Outputs; out last_ping;
   --# derives Bus.Outputs from *, sx, sy &
   --#         last_ping from sx, sy;
   is
   begin
      -- Mark the last requested ping accordingly
      Last_Ping := Ping_Request'
        (Sx => Sx,
         Sy => Sy,
         Fresh_Request => True,
         Fresh_Answer => False,
         Distance => 0,
         Velocity => 0);
      -- Write on 2T
      bc1553.Write_Word(Data => State_Types.Radar_values(State_Types.Ping),
                        Idx => 1,
                        Subaddress_Idx => 2,
                        Dest => Bus_id);
      Bc1553.Write_Word(Data => Radar_Cfg.Encode_Sector(Sx),
                        Idx => 2,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
      Bc1553.Write_Word(Data => Radar_Cfg.Encode_Sector(Sy),
                        Idx => 4,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
   end Ping;

   -- Sweep the radar
   procedure Sweep(Sx_Start, Sx_End : in Radar_Cfg.Sector_Range;
                   Sy_Start, Sy_End : in Radar_Cfg.Sector_Range)
   --# global in out bus.outputs; out last_sweep;
   --# derives bus.outputs from *, sx_start, sx_end,
   --#          sy_start, sy_end &
   --#    last_sweep from sx_start, sx_end,
   --#          sy_start, sy_end;
   is
   begin
     -- Mark the last requested ping accordingly
      Last_Sweep := Sweep_Request'
        (Sx_start => Sx_start,
         Sx_End   => Sx_End,
         Sy_Start => Sy_Start,
         Sy_End   => Sy_End,
         Fresh_Request => True,
         Fresh_Answer => False,
         Grid => Measuretypes.Bit4_Array'
         (others => Measuretypes.Bit4_Slice'(others => False))
         );
      -- Write on 2T
      bc1553.Write_Word(Data => State_Types.Radar_values(State_Types.Sweep),
                        Idx => 1,
                        Subaddress_Idx => 2,
                        Dest => Bus_id);
      Bc1553.Write_Word(Data => Radar_Cfg.Encode_Sector(Sx_start),
                        Idx => 2,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
      Bc1553.Write_Word(Data => Radar_Cfg.Encode_Sector(Sx_end),
                        Idx => 3,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
      Bc1553.Write_Word(Data => Radar_Cfg.Encode_Sector(Sy_start),
                        Idx => 4,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
      Bc1553.Write_Word(Data => Radar_Cfg.Encode_Sector(Sy_end),
                        Idx => 5,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
   end Sweep;

   procedure Read_Ping(Sx,Sy : out Radar_Cfg.Sector_Range;
                       Dist  : out Measuretypes.Meter;
                       Vel   : out Measuretypes.Meter_Per_Sec)
   --# global in last_ping;
   --# derives sx, sy, dist, vel from last_ping;
   is
   begin
      if Last_Ping.Fresh_Answer then
         Sx := Last_Ping.Sx;
         Sy := Last_Ping.Sx;
         Dist := Last_Ping.Distance;
         Vel := Last_Ping.Velocity;
      else
         Sx := 0;
         Sy := 0;
         Dist := 0;
         Vel := 0;
      end if;
   end Read_Ping;

   procedure Read_sweep(Sx_start,Sx_end : out Radar_Cfg.Sector_Range;
                        Sy_Start,Sy_End : out Radar_Cfg.Sector_Range;
                        Grid : out Measuretypes.Bit4_Array)
   --# global in last_sweep;
   --# derives sx_start, sx_end, sy_start, sy_end,
   --#         grid from last_sweep;
   is
   begin
      if Last_Sweep.Fresh_Answer then
         Sx_Start := Last_Sweep.Sx_Start;
         Sx_End   := Last_Sweep.Sx_end;
         Sy_Start := Last_Sweep.Sy_Start;
         Sy_End   := Last_Sweep.Sy_end;
         Grid := Last_Sweep.Grid;
      else
         Sx_Start := 0;
         Sx_end := 0;
         Sy_Start := 0;
         Sy_end := 0;
         Grid := Measuretypes.Bit4_Array'
           (others => Measuretypes.Bit4_Slice'(others => False));
      end if;
   end Read_Sweep;

   -- Kick off a radar IBIT
   procedure Ibit_Start
     --# global in out Bus.Outputs;
     --#        out    Ibit_Request;
   --# derives Bus.Outputs from * &
   --#         Ibit_Request from ;
   is
      Code : SystemTypes.Byte;
   begin
      Ibit_Request := IBIT.Request_Start;
      Code := IBIT.Phase_Lookup(Ibit_Request);
      -- Send it out on 1R at word 1
      BC1553.Write_Word(Data => Code,
                        Idx =>  1,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Ibit_Start;

   -- Stop a radar IBIT
   procedure Ibit_Stop
   --# global in out Bus.Outputs;
   --#    out Ibit_Request;
   --# derives Bus.Outputs from * &
   --#         Ibit_Request from ;
   is
      Code : SystemTypes.Byte;
   begin
      Ibit_Request := IBIT.Request_Stop;
      Code := IBIT.Phase_Lookup(Ibit_Request);
      -- Send it out on 1R at word 1
      BC1553.Write_Word(Data => Code,
                        Idx =>  1,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Ibit_Stop;

   -- Poll the bus and update states
   procedure Poll
   --# global in out Last_ping, last_sweep, Ibit_Request;
   --#        in Bus.Inputs;
   --# derives Last_ping, last_sweep,
   --#         Ibit_Request from *, Bus.Inputs;
   is
      Word : Bus.Word;
      New_State : State_Types.Radar;
      Dist : Measuretypes.Meter;
      Vel : Measuretypes.Meter_Per_Sec;
   begin
      -- Check 2T
      if BC1553.Is_Valid(Src => Bus_id,
                         Subaddress_Idx => 2) and then
        BC1553.Is_Fresh(Src => Bus_id,
                        Subaddress_Idx => 2) then
         -- Read the state
         BC1553.Read_Word(Src => Bus_id,
                          Idx => 1,
                          Subaddress_Idx => 2,
                          Data => Word);
         New_State := State_Types.Radar_Action(Word);
         case New_State is
            when State_Types.Rad_Inactive =>
               null;
            when State_Types.Ping =>
               -- dist is in idx 2, vel is in idx 3
               BC1553.Read_Word(Src => Bus_id,
                                Idx => 2,
                                Subaddress_Idx => 2,
                                Data => Word);
               Dist := Measuretypes.Decode.Meter_Single(Word);
               BC1553.Read_Word(Src => Bus_id,
                                Idx => 3,
                                Subaddress_Idx => 2,
                                Data => Word);
               Vel  := Measuretypes.Decode.Meter_Per_Sec(Word);
               Last_Ping.Fresh_Answer := True;
               Last_Ping.Distance := Dist;
               Last_Ping.Velocity := Vel;
            when State_Types.Sweep =>
               -- Grid is in idx 2
               BC1553.Read_Word(Src => Bus_id,
                                Idx => 2,
                                Subaddress_Idx => 2,
                                Data => Word);
               Last_Sweep.Grid := Measuretypes.Decode.Bit4_Array(Word);
               Last_Sweep.Fresh_Answer := True;
         end case;
      else
         -- Nothing to do
         null;
      end if;

      -- 1T word 1 - BIT
      BC1553.Read_Word(Src => Bus_id,
                       Idx => 1,
                       Subaddress_Idx => 1,
                       Data => Word);
      -- Use the standard state machine to transform
      -- our IBIT phase
      IBIT.State_Machine(Bus_Data => Word,
                         Current_Phase => IBIT_Request);
   end Poll;

   -- Initialise
   procedure Init
   --# global out Last_ping, last_sweep, Ibit_Request;
   --#        in out Bus.Outputs;
   --# derives Last_ping, last_sweep, Ibit_Request from &
   --#         Bus.Outputs from *;
   is begin
      Last_Ping := Null_Ping;
      Last_Sweep := Null_Sweep;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => Bus_id,
                               Subaddress_Idx => 1);
      Bc1553.Set_Message_Valid(Subaddress_Idx => 2,
                               dest => Bus_Id);
   end Init;

   -- Test point
   procedure Command is separate;

end If_Radar;
