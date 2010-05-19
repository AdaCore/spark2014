-- MCU interface to the fuel tank, implementation
--
-- $Log: if_fuel.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/10 20:59:21  adi
-- Added get_ibit_state
--
-- Revision 1.1  2003/08/17 12:49:16  adi
-- Initial revision
--
--
with Bc1553, bus;
package body If_Fuel
  --# own State is Last_Level, Last_Valid, Ibit_Request;
is
   Last_Level : Measuretypes.Kilo := 0;
      Last_Valid  : Boolean := False;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   Bus_Id : constant Bc1553.Lru_Name := Bc1553.Fuel;

   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
   end Get_Ibit_State;

   -- Find out the current level and its validity
   procedure Get_Level(Level : out measuretypes.kilo;
                        Valid  : out Boolean)
   --# global in Last_Level, Last_Valid;
   --# derives Level from Last_Level, Last_Valid &
   --#        Valid from Last_Valid;
   is
   begin
      Valid := Last_Valid;
      if Last_Valid then
         Level := Last_Level;
      else
         Level := 0;
      end if;
   end Get_Level;

   -- Kick off a fuel IBIT
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

   -- Stop a fuel IBIT
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
   --# global in out Last_Level, Last_Valid, Ibit_Request;
   --#        in Bus.Inputs;
   --# derives Last_Level, Last_Valid,
   --#         Ibit_Request from *, Bus.Inputs;
   is
      Word : Bus.Word;
   begin
      -- Check 1T
      if BC1553.Is_Valid(Src => Bus_id,
                         Subaddress_Idx => 1) and then
        BC1553.Is_Fresh(Src => Bus_id,
                        Subaddress_Idx => 1) then
         Bc1553.Read_Word(Src => Bus_Id,
                          Idx => 1,
                          Subaddress_Idx => 1,
                          Data => Word);
         Last_Level := Measuretypes.Kilo(Word);
         Last_Valid := True;
         -- 1T word 2 - BIT
         BC1553.Read_Word(Src => Bus_id,
                          Idx => 2,
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
   --# global out Last_Level, Last_Valid, Ibit_Request;
   --#        in out Bus.Outputs;
   --# derives Last_Level, Last_Valid, Ibit_Request from &
   --#         Bus.Outputs from *;
   is begin
      Last_Level := 0;
      Last_Valid := False;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => Bus_id,
                               Subaddress_Idx => 1);
   end Init;

   -- Test point
   procedure Command is separate;

end If_Fuel;
