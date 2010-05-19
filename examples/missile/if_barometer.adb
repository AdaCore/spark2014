-- MCU interface to the barometer, implementation
--
-- $Log: if_barometer.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.4  2003/09/10 20:09:10  adi
-- Added IBIT state accessor
--
-- Revision 1.3  2003/02/19 19:11:48  adi
-- Added Command stub
--
-- Revision 1.2  2003/02/12 23:23:03  adi
-- Added Init procedure
--
-- Revision 1.1  2003/02/11 20:37:18  adi
-- Initial revision
--
--
with Bc1553, bus;
package body If_Barometer
  --# own State is Last_Height, Last_Valid, Ibit_Request;
is
   Last_Height : MeasureTypes.Meter := 0;
   Last_Valid  : Boolean := False;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   -- Find out the current IBIT state
   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
   end Get_Ibit_State;

   -- Find out the current height and its validity
   procedure Get_Height(Height : out MeasureTypes.Meter;
                        Valid  : out Boolean)
   --# global in Last_Height, Last_Valid;
   --# derives Height from Last_Height, Last_Valid &
   --#        Valid from Last_Valid;
   is
   begin
      Valid := Last_Valid;
      if Last_Valid then
         Height := Last_Height;
      else
         Height := 0;
      end if;
   end Get_Height;

   -- Kick off a barometer IBIT
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
                        Dest => BC1553.Barometer);
   end Ibit_Start;

   -- Stop a barometer IBIT
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
                        Dest => BC1553.Barometer);
   end Ibit_Stop;

   -- Poll the bus and update states
   procedure Poll
   --# global in out Last_Height, Last_Valid, Ibit_Request;
   --#        in Bus.Inputs;
   --# derives Last_Height, Last_Valid,
   --#         Ibit_Request from *, Bus.Inputs;
   is
      Word : Bus.Word;
   begin
      -- Check 1T
      if BC1553.Is_Valid(Src => Bc1553.Barometer,
                         Subaddress_Idx => 1) and then
        BC1553.Is_Fresh(Src => Bc1553.Barometer,
                        Subaddress_Idx => 1) then
         -- 1T word 1 - hi part of altitude
         BC1553.Read_Word(Src => BC1553.Barometer,
                          Idx => 1,
                          Subaddress_Idx => 1,
                          Data => Word);
         Last_Height := 256 * MeasureTypes.Meter(Word);
         -- 1T word 2 - lo part of altitude
         BC1553.Read_Word(Src => BC1553.Barometer,
                          Idx => 2,
                          Subaddress_Idx => 1,
                          Data => Word);
         Last_Height := Last_Height + MeasureTypes.Meter(Word);
         -- And now height is valid
         Last_Valid := True;
         -- 1T word 3 - BIT
         BC1553.Read_Word(Src => BC1553.Barometer,
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
   --# global out Last_Height, Last_Valid, Ibit_Request;
   --#        in out Bus.Outputs;
   --# derives Last_Height, Last_Valid, Ibit_Request from &
   --#         Bus.Outputs from *;
   is begin
      Last_Height := 0;
      Last_Valid := False;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => BC1553.Barometer,
                               Subaddress_Idx => 1);
   end Init;

   -- Test point
   procedure Command is separate;
end If_Barometer;
