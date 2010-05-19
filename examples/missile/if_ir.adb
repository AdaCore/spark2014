-- MCU interface to the IR, implementation
--
-- $Log: if_ir.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/11 19:48:03  adi
-- Added get_ibit_state
--
-- Revision 1.1  2003/08/27 21:01:32  adi
-- Initial revision
--
--
with Bc1553, Bus, State_Types, Measuretypes.decode;
package body If_Ir
  --# own State is
  --#     Last_stare, Last_sweep, Ibit_Request;
is
   subtype Sector is Ir_Cfg.Sector_Range;
   type Stare_Request is record
      Sx, Sy : Sector;
      Fresh_Request, Fresh_Answer : Boolean;
      Temp : Measuretypes.Kelvin;
   end record;

   type Sweep_Request is record
      Sx_Start, Sx_End : Sector;
      Sy_Start, Sy_End : Sector;
      Fresh_Request, Fresh_Answer : Boolean;
      Grid : Measuretypes.Bit4_Array;
   end record;

   Null_Stare : constant Stare_Request
     := Stare_Request'(Sx => 0,
                      Sy => 0,
                      Fresh_Request => False,
                       Fresh_Answer => False,
                       Temp => 0);

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

   Last_Stare : Stare_Request := Null_stare;
   Last_Sweep : Sweep_Request := Null_sweep;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   Bus_Id : constant Bc1553.Lru_Name := Bc1553.Infrared;

   -- Get the IBIT state
   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
      end Get_Ibit_State;

   -- Stare the ir
   procedure Stare(Sx, Sy : in Ir_Cfg.Sector_Range)
   --# global in out Bus.Outputs; out last_stare;
   --# derives Bus.Outputs from *, sx, sy &
   --#         last_stare from sx, sy;
   is
   begin
      -- Mark the last requested stare accordingly
      Last_Stare := Stare_Request'
        (Sx => Sx,
         Sy => Sy,
         Fresh_Request => True,
         Fresh_Answer => False,
         Temp => 0);
      -- Write on 2T
      bc1553.Write_Word(Data => State_Types.Ir_values(State_Types.Ir_Stare),
                        Idx => 1,
                        Subaddress_Idx => 2,
                        Dest => Bus_id);
      Bc1553.Write_Word(Data => Ir_Cfg.Encode_Sector(Sx),
                        Idx => 2,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
      Bc1553.Write_Word(Data => Ir_Cfg.Encode_Sector(Sy),
                        Idx => 4,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
   end Stare;

   -- Sweep the ir
   procedure Sweep(Sx_Start, Sx_End : in Ir_Cfg.Sector_Range;
                   Sy_Start, Sy_End : in Ir_Cfg.Sector_Range)
   --# global in out bus.outputs; out last_sweep;
   --# derives bus.outputs from *, sx_start, sx_end,
   --#          sy_start, sy_end &
   --#    last_sweep from sx_start, sx_end,
   --#          sy_start, sy_end;
   is
   begin
     -- Mark the last requested stare accordingly
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
      bc1553.Write_Word(Data => State_Types.Ir_values(State_Types.Ir_Sweep),
                        Idx => 1,
                        Subaddress_Idx => 2,
                        Dest => Bus_id);
      Bc1553.Write_Word(Data => Ir_Cfg.Encode_Sector(Sx_start),
                        Idx => 2,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
      Bc1553.Write_Word(Data => Ir_Cfg.Encode_Sector(Sx_end),
                        Idx => 3,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
      Bc1553.Write_Word(Data => Ir_Cfg.Encode_Sector(Sy_start),
                        Idx => 4,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
      Bc1553.Write_Word(Data => Ir_Cfg.Encode_Sector(Sy_end),
                        Idx => 5,
                        Subaddress_Idx => 2,
                        Dest => Bus_Id);
   end Sweep;

   procedure Read_Stare(Sx,Sy : out Ir_Cfg.Sector_Range;
                        Temp : out Measuretypes.Kelvin)
   --# global in last_stare;
   --# derives sx, sy, temp from last_stare;
   is
   begin
      if Last_Stare.Fresh_Answer then
         Sx := Last_Stare.Sx;
         Sy := Last_Stare.Sx;
         Temp := Last_Stare.Temp;
      else
         Sx := 0;
         Sy := 0;
         Temp := 0;
      end if;
   end Read_Stare;

   procedure Read_sweep(Sx_start,Sx_end : out Ir_Cfg.Sector_Range;
                        Sy_Start,Sy_End : out Ir_Cfg.Sector_Range;
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

   -- Kick off a ir IBIT
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

   -- Stop a ir IBIT
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
   --# global in out Last_stare, last_sweep, Ibit_Request;
   --#        in Bus.Inputs;
   --# derives Last_stare, last_sweep,
   --#         Ibit_Request from *, Bus.Inputs;
   is
      Word : Bus.Word;
      New_State : State_Types.Infrared;
      Temp : Measuretypes.Kelvin;
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
         New_State := State_Types.Ir_Action(Word);
         case New_State is
            when State_Types.ir_Inactive =>
               null;
            when State_Types.Ir_Stare =>
               -- temp is in idx 2
               BC1553.Read_Word(Src => Bus_id,
                                Idx => 2,
                                Subaddress_Idx => 2,
                                Data => Word);
               temp := Measuretypes.Decode.kelvin(Word);
               Last_Stare.Fresh_Answer := True;
               Last_Stare.Temp := Temp;
            when State_Types.Ir_Sweep =>
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
   --# global out Last_stare, last_sweep, Ibit_Request;
   --#        in out Bus.Outputs;
   --# derives Last_stare, last_sweep, Ibit_Request from &
   --#         Bus.Outputs from *;
   is begin
      Last_Stare := Null_Stare;
      Last_Sweep := Null_Sweep;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => Bus_id,
                               Subaddress_Idx => 1);
      Bc1553.Set_Message_Valid(Subaddress_Idx => 2,
                               dest => Bus_Id);
   end Init;

   -- Test point
   procedure Command is separate;

end If_Ir;
