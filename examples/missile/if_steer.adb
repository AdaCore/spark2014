-- MCU interface to the fins, implementation
--
-- $Log: if_steer.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/11 19:54:08  adi
-- Added get_ibit_state
--
-- Revision 1.1  2003/08/31 20:28:55  adi
-- Initial revision
--
--
with
  Systemtypes,
  Bc1553,
  Bus,
  Steer_Cfg.Encode,
  Steer_Cfg.decode;
package body If_Steer
  --# own State is Last_fins, last_valid, Ibit_Request;
is
   type Fin_Angles is array(Fin) of angle;
   Zero_Angles : constant Fin_Angles
     := Fin_Angles'(others => 0);

   Last_Fins    : Fin_Angles := Zero_Angles;
   Last_Valid   : Boolean    := False;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   Bus_Id : constant Bc1553.Lru_Name := Bc1553.Fins;

   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
   end Get_Ibit_State;

   -- Find out a fin deflection
   procedure Get_deflection(For_Fin : in Fin;
                            This_Angle : out Angle;
                            Valid  : out Boolean)
   --# global in last_fins, Last_Valid;
   --# derives this_angle from for_fin, last_fins, Last_Valid &
   --#        Valid from Last_Valid;
   is
   begin
      Valid := Last_Valid;
      if Last_Valid then
         This_Angle := Last_Fins(For_Fin);
      else
         This_Angle := 0;
      end if;
   end Get_deflection;

   -- Command a fin steering deflection
   procedure Set_Deflection(For_Fin : in Fin;
                            New_Angle : in Angle)
   is
      Idx : Bus.Word_Index;
      Datum : Bus.Word;
   begin
      Datum := Steer_Cfg.Encode.Fin_Angle(New_Angle);
      case For_Fin is
         when Steer_Cfg.Port =>
            Idx := 1;
         when Steer_Cfg.Starboard =>
            Idx := 2;
         when Steer_Cfg.Top =>
            Idx := 3;
         when Steer_Cfg.Bottom =>
            Idx := 4;
      end case;
      BC1553.Write_Word(Data => Datum,
                        Idx =>  Idx,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Set_Deflection;


   -- Kick off a steer IBIT
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
      -- Send it out on 1R at word 5
      BC1553.Write_Word(Data => Code,
                        Idx =>  5,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Ibit_Start;

   -- Stop a steer IBIT
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
      -- Send it out on 1R at word 5
      BC1553.Write_Word(Data => Code,
                        Idx =>  5,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Ibit_Stop;

   -- Poll the bus and update states
   procedure Poll
   --# global in out last_fins, Last_Valid, Ibit_Request;
   --#        in Bus.Inputs;
   --# derives last_fins, Last_Valid,
   --#         Ibit_Request from *, Bus.Inputs;
   is
      Datum : Bus.Word;

      procedure Update_Fin(For_Fin : in Fin;
                           Idx : in Bus.Word_Index)
        --# global in bus.inputs;
        --#    in out last_fins;
        --# derives last_fins from *, for_fin, idx, bus.inputs;
      is
         Word : Bus.Word;
         A : Angle;
      begin
         BC1553.Read_Word(Src => Bus_id,
                          Idx => idx,
                          Subaddress_Idx => 1,
                          Data => Word);
         A := Steer_Cfg.Decode.Fin_Angle(Word);
         Last_Fins(For_Fin) := A;
      end Update_Fin;
   begin
      -- Check 1T
        if BC1553.Is_Valid(Src => Bus_id,
                           Subaddress_Idx => 1) and then
          BC1553.Is_Fresh(Src => Bus_id,
                        Subaddress_Idx => 1) then
           -- Continuous check
           Update_Fin(For_Fin => Steer_Cfg.Port,
                      Idx => 1);
           Update_Fin(For_Fin => Steer_Cfg.Starboard,
                      Idx => 2);
           Update_Fin(For_Fin => Steer_Cfg.Top,
                      Idx => 3);
           Update_Fin(For_Fin => Steer_Cfg.Bottom,
                      Idx => 4);
           Last_Valid := True;
           -- 1T word 5 - BIT
           BC1553.Read_Word(Src => Bus_id,
                            Idx => 5,
                            Subaddress_Idx => 1,
                            Data => datum);
           -- Use the standard state machine to transform
           -- our IBIT phase
           IBIT.State_Machine(Bus_Data => datum,
                              Current_Phase => IBIT_Request);
        else
           -- Nothing to do
           null;
        end if;
   end Poll;

   -- Initialise
   procedure Init
   --# global out last_fins, Last_Valid, Ibit_Request;
   --#        in out Bus.Outputs;
   --# derives last_fins, Last_Valid, Ibit_Request from &
   --#         Bus.Outputs from *;
   is begin
      Last_Fins := Zero_angles;
      Last_Valid := False;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => Bus_id,
                               Subaddress_Idx => 1);
   end Init;

   -- Test point
   procedure Command is separate;

end If_Steer;
