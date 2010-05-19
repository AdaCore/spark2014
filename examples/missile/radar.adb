-- Radar simulator implementation
--
-- $Log: radar.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.4  2003/08/25 20:37:50  adi
-- Fixed overflow error in derive_grid
--
-- Revision 1.3  2003/08/25 20:31:30  adi
-- Fixed feedback of message
--
-- Revision 1.2  2003/08/25 19:37:01  adi
-- Use of radar_cfg.encode
--
-- Revision 1.1  2003/08/25 13:34:30  adi
-- Initial revision
--
--
with SystemTypes,State_Types,Measuretypes.encode;
with Bus,RT1553,IBIT,Bit_Machine;
package body Radar
  --# own State is
  --#     detect_points,
  --#     rand_seed,
  --#     BIT_State;
is
   subtype Integer32 is Systemtypes.Integer32;

   type Ping is record
      Distance : Meter;
      Rel_Vel  : Meter_Per_Sec;
   end record;

   Zero_Ping : constant Ping :=
     Ping'(Distance => 0, Rel_Vel => 0);

   type Sector_Slice is array(Sector) of Ping;
   type Sector_Array is array(Sector) of Sector_slice;

   Detect_Points : Sector_Array :=
     Sector_Array'(others => Sector_Slice'(others => Zero_Ping));
   Rand_Seed : Random.Number := Random.Null_seed;
   Bit_State  : Bit_Machine.Machine := Bit_Machine.Initial_Machine;

   Bus_Id : constant Rt1553.Lru_Name := Rt1553.Radar;

   --------- Public subprograms

    procedure Set_Bearing_Return(Sx, Sy : in Sector;
                                D : in Meter;
                                V : in Meter_Per_sec)
   --# global in out detect_points;
   --# derives detect_points from *, Sx, Sy, D, V;
    is begin
       Detect_Points(Sx)(Sy) :=
         Ping'(Distance => D, Rel_Vel => V);
    end Set_Bearing_Return;

     -- Read what's at a bearing
   procedure Read_Location(Sx, Sy : in Sector;
                           D : out Meter;
                           V : out Meter_Per_sec)
   --# global in detect_points;
   --# derives D, V from detect_points, Sx, Sy;
   is begin
      D := Detect_Points(Sx)(Sy).Distance;
      V := Detect_Points(Sx)(Sy).Rel_Vel;
   end Read_Location;

   procedure Do_Ping(Sx, Sy : in Sector)
     --# global in detect_points;
     --#        in out rand_seed;
     --#        in out bus.inputs;
     --#   derives bus.inputs from
     --#    *, Sx, Sy, detect_points, rand_seed &
     --#    rand_seed from *;
   is
      Datum : Bus.Word;
      Distance : Meter;
      Vel : Meter_Per_Sec;
      V : Random.Value;
   begin
      Random.Get(N => Rand_Seed,
                 V => V);
      -- Write out Ping results to T2 word 1, 2, 3
      --   in order:  "Ping", Distance, Velocity
      Rt1553.Write_Word(Data =>
                          State_Types.Radar_Values(State_Types.Ping),
                       Idx => 1,
                       Subaddress_Idx => 2,
                        Src => Bus_id);
      -- Work out the distance
      Distance := Detect_Points(Sx)(Sy).distance;
      -- Random fluctuation in distance by up to 200m
      Distance := Distance + meter(V mod 200);
      Datum :=
        Measuretypes.Encode.Meter_Single(M => Distance,
                                         R => Radar_Cfg.Max_Detect_range);
      Rt1553.Write_Word(Data => Datum,
                        Idx => 2,
                        Subaddress_Idx => 2,
                        Src => Bus_Id);
      -- Work out the relative velocity
      Random.Get(N => Rand_Seed,
                 V => V);
      Vel := Detect_Points(Sx)(Sy).Rel_Vel;
      -- Random fluctuation in speed by up to 20m/s
      Vel := Vel + Meter_Per_Sec(V mod 20);
      Measuretypes.Encode.Meter_Per_Sec(V => Vel,
                                        W => Datum);
      Rt1553.Write_Word(Data => Datum,
                        Idx => 3,
                        Subaddress_Idx => 2,
                        Src => Bus_Id);
   end Do_Ping;

   -- Sweep grid between Xs and Ys.
   -- Send a 4x4 bit grid showing the found/not found in the quarters
   procedure Sweep(x_Start, x_End : in Sector;
                   Y_Start, Y_End : in Sector)
     --# global in detect_points;
     --#        in out bus.inputs;
     --# derives bus.inputs from
     --#    *, x_start, x_end,
     --#       y_start, y_end, detect_points;
   is
      Bit_data : Bus.Word;
      Detect : Measuretypes.Bit4_Array;

      procedure Derive_Grid
        --# global out detect;
        --#         in detect_points, x_start, x_end, y_start, y_end;
        --# derives detect from detect_points,
        --#       x_start, x_end, y_start, y_end;
      is
        Actual_X, Actual_Y : Measuretypes.bit4_Range;
        Dx,Ddx, Dy, ddy : integer32;
      begin
         Detect :=
           Measuretypes.Bit4_Array'(others =>
                                      Measuretypes.Bit4_Slice'(others =>
                                                                 False));
         Dx := Integer32(X_End) - Integer32(X_Start);
         Dy := Integer32(Y_End) - Integer32(Y_Start);
         for X in Sector range X_Start .. X_End loop
            --# assert x >= x_start and x <= x_end;
            Ddx := Integer32(X) - Integer32(X_Start);
            Actual_X := Measuretypes.bit4_Range((4 * ddx)/(Dx+1));
            for Y in Sector range Y_Start .. Y_End loop
               --# assert x >= x_start and x <= x_end and
               --#        y >= y_start and y <= y_end;
               Ddy := Integer32(Y) - Integer32(Y_Start);
               Actual_y := Measuretypes.bit4_Range((4 * ddy)/(Dy+1));
               if Detect_Points(X)(Y).Distance > 0 then
                  -- Detection
                  Detect(Actual_X)(Actual_Y) := True;
               end if;
            end loop;
         end loop;
      end Derive_Grid;

   begin
      Derive_Grid;
      -- Write out Detect in 1 word
      Rt1553.Write_Word(Data =>
                          State_Types.Radar_Values(State_Types.sweep),
                       Idx => 1,
                       Subaddress_Idx => 2,
                        Src => Bus_id);
      Bit_data := Measuretypes.Encode.Bit4_array(Detect);
      Rt1553.Write_Word(Data => Bit_data,
                        Idx => 2,
                        Subaddress_Idx => 2,
                        Src => Bus_Id);
   end Sweep;

   -- Read a sector value from a bus word
   procedure Read_Sector(Idx : in Bus.Word_Index;
                         Subaddress_Idx : in Bus.Lru_subaddress_Index;
                         S : out Sector)
     --# global in bus.outputs;
     --# derives s from idx, subaddress_idx, bus.outputs;
   is
      S_Datum : Bus.Word;
   begin
      Rt1553.Read_Word(Src => Bus_Id,
                       Idx => idx,
                       Subaddress_Idx => Subaddress_idx,
                       Data => S_Datum);
      S := Radar_Cfg.Decode_Sector(S_Datum);
   end Read_Sector;

      -- Cycle the reading of data from the bus
   -- and writing of data to the bus
   procedure Cycle
     --# global in detect_points;
     --#        in out rand_seed;
     --#        in out BIT_State;
     --#        in Bus.Outputs;
     --#        in out Bus.Inputs;
     --# derives
     --#        BIT_State
     --#          from *, Bus.Outputs &
     --#        rand_seed
     --#          from *, bus.outputs &
     --#        Bus.Inputs
     --#          from *,
     --#               bus.outputs,
     --#               detect_points,
     --#               rand_seed,
     --#               BIT_State;
   is
      Datum : Bus.Word;
      Remote_Command : State_Types.Radar;
      Sx1, Sx2, Sy1, Sy2, Tmp_s : Sector;

   begin
      -- Read the BIT info off R1 word 1
      Rt1553.Read_Word(Src => Bus_id,
                       Idx => 1,
                       Subaddress_Idx => 1,
                       Data => Datum);
      BIT_Machine.Change_State(Word => Datum,
                               State => Bit_state);
      -- See if R2 is updated
      Remote_Command := State_Types.Rad_Inactive;
      Sx1 := Sector'First; Sx2 := Sector'Last;
      Sy1 := Sector'First; Sy2 := Sector'Last;
      if Rt1553.Is_Valid(Src => Bus_Id,
                         Subaddress_Idx => 2) and then
        Rt1553.Is_Fresh(Src => Bus_Id,
                        Subaddress_Idx => 2) then
         -- Read in the radar command
         Rt1553.Read_Word(Src => Bus_Id,
                          Idx => 1,
                          Subaddress_Idx => 2,
                          Data => Datum);
         Remote_Command := State_Types.Radar_Action(Datum);
         case Remote_Command is
            when State_Types.Rad_Inactive =>
               null;
            when State_Types.Ping =>
               -- Do a ping on a specific sector
               Read_Sector(Idx => 2,
                           Subaddress_Idx => 2,
                           S => Sx1);
               Sx2 := Sx1;
               Read_Sector(Idx => 4,
                           Subaddress_Idx => 2,
                           S => Sy1);
               Sy2 := Sy1;
            when State_Types.Sweep =>
               -- Sweep between two sectors
               Read_Sector(Idx => 2,
                           Subaddress_Idx => 2,
                           S => Sx1);
               Read_Sector(Idx => 3,
                           Subaddress_Idx => 2,
                           S => Sx2);
               Read_Sector(Idx => 4,
                           Subaddress_Idx => 2,
                           S => Sy1);
               Read_Sector(Idx => 5,
                           Subaddress_Idx => 2,
                           S => Sy2);
               -- Ensure S1 <= S2
               if (Sx1 > Sx2) then
                 Tmp_S := Sx1; Sx1 := Sx2; Sx2 := Tmp_S;
               end if;
               if (Sy1 > Sy2) then
                 Tmp_S := Sy1; Sy1 := Sy2; Sy2 := Tmp_S;
               end if;
         end case;
      end if;
      --# assert Sx1 <= Sx2 and Sy1 <= Sy2;
      -- And cycle the BIT
      BIT_Machine.Step(Bit_State);

      -- Write the BIT phase to T1 word 1
      Rt1553.Write_Word(Data =>
                          IBIT.Phase_Lookup(BIT_Machine.Phase(Bit_State)),
                       Idx => 1,
                       Subaddress_Idx => 1,
                       Src => Bus_id);

      -- Write out the results of a ping or sweep
      case Remote_Command is
         when State_Types.Rad_Inactive =>
            null;
         when State_Types.ping =>
            -- Do a ping on S1
            Do_Ping(Sx1,Sy1);
         when State_Types.sweep =>
            -- Sweep between S1 and S2;
            Sweep(Sx1,Sx2,Sy1,Sy2);
      end case;
   end Cycle;

   procedure Fail_Next_Bit
     --# global in out BIT_State;
     --# derives BIT_State from *;
   is begin
      BIT_Machine.Fail_Next(Bit_State);
   end Fail_Next_Bit;

   procedure Init
     --# global out detect_points, rand_seed, BIT_State;
     --#        in out Bus.Inputs;
     --# derives detect_points, rand_seed, BIT_State from &
     --#        Bus.Inputs from *;
   is begin
      -- Initialise the bus message 1T and 2T
      RT1553.Set_Message_Valid(Subaddress_Idx => 1,
                               Src => Bus_id);
      RT1553.Set_Message_Valid(Subaddress_Idx => 2,
                               Src => Bus_id);
      -- Initialise the variables
      Detect_Points := Sector_Array'(others =>
                                       Sector_Slice'(others => Zero_Ping));
      Rand_Seed := Random.Seed(45);
      BIT_Machine.Create(Ticks_To_Complete => 65,
                         State => Bit_State);
   end Init;

   procedure Command is separate;
end radar;
