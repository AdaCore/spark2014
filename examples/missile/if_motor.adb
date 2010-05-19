-- MCU interface to the motor, implementation
--
-- $Log: if_motor.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/11 19:50:46  adi
-- Added get_ibit_state
--
-- Revision 1.1  2003/09/01 18:28:45  adi
-- Initial revision
--
--
with
  Systemtypes,
  Bc1553,
  Bus,
  measuretypes.Encode,
  measuretypes.decode;
package body If_Motor
  --# own State is Last_thrust, last_valid, Ibit_Request;
is
   Last_Thrust  : Power := Power'First;
   Last_Valid   : Boolean    := False;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   Bus_Id : constant Bc1553.Lru_Name := Bc1553.Motor;

   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
   end Get_Ibit_State;

   -- Find out a fin thrust
   procedure Get_thrust(This_Level : out Power;
                        Valid  : out Boolean)
   --# global in last_thrust, Last_Valid;
   --# derives this_level from last_thrust, Last_Valid &
   --#        Valid from Last_Valid;
   is
   begin
      Valid := Last_Valid;
      if Last_Valid then
         This_level := Last_Thrust;
      else
         This_level := Power'first;
      end if;
   end Get_thrust;

   -- Command a motoring thrust
   procedure Set_Thrust(New_Level : in Power)
   is
      Dlo,dhi : Bus.Word;
   begin
      Measuretypes.Encode.Newton(N => New_Level,
                                 Lo => Dlo,
                                 Hi => Dhi);
      BC1553.Write_Word(Data => Dlo,
                        Idx =>  1,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
      BC1553.Write_Word(Data => Dhi,
                        Idx =>  2,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Set_Thrust;


   -- Kick off a motor IBIT
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
      -- Send it out on 1R at word 3
      BC1553.Write_Word(Data => Code,
                        Idx =>  3,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Ibit_Start;

   -- Stop a motor IBIT
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
      -- Send it out on 1R at word 3
      BC1553.Write_Word(Data => Code,
                        Idx =>  3,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Ibit_Stop;

   -- Poll the bus and update states
   procedure Poll
   --# global in out last_thrust, Last_Valid, Ibit_Request;
   --#        in Bus.Inputs;
   --# derives last_thrust, Last_Valid,
   --#         Ibit_Request from *, Bus.Inputs;
   is
      Datum, Dlo, dhi : Bus.Word;
   begin
      -- Check 1T
        if BC1553.Is_Valid(Src => Bus_id,
                           Subaddress_Idx => 1) and then
          BC1553.Is_Fresh(Src => Bus_id,
                          Subaddress_Idx => 1) then
           BC1553.Read_Word(Src => Bus_id,
                            Idx => 1,
                            Subaddress_Idx => 1,
                            Data => dlo);
           BC1553.Read_Word(Src => Bus_id,
                            Idx => 2,
                            Subaddress_Idx => 1,
                            Data => dhi);
           Last_Thrust := Measuretypes.Decode.Newton(Lo => Dlo, Hi => Dhi);
           Last_Valid := True;
           -- 1T word 3 - BIT
           BC1553.Read_Word(Src => Bus_id,
                            Idx => 3,
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
   --# global out last_thrust, Last_Valid, Ibit_Request;
   --#        in out Bus.Outputs;
   --# derives last_thrust, Last_Valid, Ibit_Request from &
   --#         Bus.Outputs from *;
   is begin
      Last_Thrust := Power'First;
      Last_Valid := False;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => Bus_id,
                               Subaddress_Idx => 1);
   end Init;

   -- Test point
   procedure Command is separate;

end If_Motor;
