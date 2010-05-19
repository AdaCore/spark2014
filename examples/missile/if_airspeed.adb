-- MCU interface to the ASI, implementation
--
-- $Log: if_airspeed.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/10 20:06:56  adi
-- Added Ibit state detection
--
-- Revision 1.1  2003/08/10 16:49:35  adi
-- Initial revision
--
--
with Bc1553, bus;
package body If_Airspeed
  --# own State is Last_Speed, Last_Valid, Ibit_Request;
is
   Last_Speed : MeasureTypes.Meter_Per_Sec := 0;
   Last_Valid  : Boolean := False;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   -- Find the current IBIT phase
   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
   end Get_Ibit_State;

   -- Find out the current speed and its validity
   procedure Get_Speed(Speed : out MeasureTypes.Meter_Per_Sec;
                        Valid  : out Boolean)
   --# global in Last_Speed, Last_Valid;
   --# derives Speed from Last_Speed, Last_Valid &
   --#        Valid from Last_Valid;
   is
   begin
      Valid := Last_Valid;
      if Last_Valid then
         Speed := Last_Speed;
      else
         Speed := 0;
      end if;
   end Get_Speed;

   -- Kick off a airspeed IBIT
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
                        Dest => BC1553.Asi);
   end Ibit_Start;

   -- Stop a airspeed IBIT
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
                        Dest => BC1553.Asi);
   end Ibit_Stop;

   -- Poll the bus and update states
   procedure Poll
   --# global in out Last_Speed, Last_Valid, Ibit_Request;
   --#        in Bus.Inputs;
   --# derives Last_Speed, Last_Valid,
   --#         Ibit_Request from *, Bus.Inputs;
   is
      Word : Bus.Word;
   begin
      -- Check 1T
      if BC1553.Is_Valid(Src => Bc1553.Asi,
                         Subaddress_Idx => 1) and then
        BC1553.Is_Fresh(Src => Bc1553.Asi,
                        Subaddress_Idx => 1) then
         -- 1T word 1 - speed
         BC1553.Read_Word(Src => BC1553.Asi,
                          Idx => 1,
                          Subaddress_Idx => 1,
                          Data => Word);
         Last_Speed := MeasureTypes.Meter_Per_Sec(Word);
         -- 1T word 2 - unused
         Last_Valid := True;
         -- 1T word 3 - BIT
         BC1553.Read_Word(Src => BC1553.Asi,
                          Idx => 3,
                          Subaddress_Idx => 1,
                          Data => Word);
         -- Use the standard state machine to transform
         -- our IBIT phase
         IBIT.State_Machine(Bus_Data => Word,
                            Current_Phase => IBIT_Request);
      else
         -- Nothing to do
         null;
      end if;
   end Poll;

   -- Initialise
   procedure Init
   --# global out Last_Speed, Last_Valid, Ibit_Request;
   --#        in out Bus.Outputs;
   --# derives Last_Speed, Last_Valid, Ibit_Request from &
   --#         Bus.Outputs from *;
   is begin
      Last_Speed := 0;
      Last_Valid := False;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => BC1553.Asi,
                               Subaddress_Idx => 1);
   end Init;

   -- Test point
   procedure Command is separate;
end If_Airspeed;
