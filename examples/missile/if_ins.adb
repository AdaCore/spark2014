-- MCU interface to the INS, implementation
--
-- $Log: if_ins.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/09/10 21:04:56  adi
-- Added get_ibit_state
--
-- Revision 1.2  2003/08/17 12:47:00  adi
-- Corrected bit read address
--
-- Revision 1.1  2003/08/12 18:09:19  adi
-- Initial revision
--
--
with Bc1553, bus;
package body If_Ins
  --# own State is Last_Position, Last_Valid, Ibit_Request;
is
   Last_Position : Cartesian.position := Cartesian.Zero_position;
   Last_Valid  : Boolean := False;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   Bus_Id : constant Bc1553.Lru_Name := Bc1553.Ins;

   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
   end Get_Ibit_State;

   -- Find out the current position and its validity
   procedure Get_Location(Position : out Cartesian.position;
                        Valid  : out Boolean)
   --# global in Last_Position, Last_Valid;
   --# derives Position from Last_Position, Last_Valid &
   --#        Valid from Last_Valid;
   is
   begin
      Valid := Last_Valid;
      if Last_Valid then
         Position := Last_Position;
      else
         Position := Cartesian.Zero_position;
      end if;
   end Get_Location;

   -- Kick off a ins IBIT
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

   -- Stop a ins IBIT
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
   --# global in out Last_Position, Last_Valid, Ibit_Request;
   --#        in Bus.Inputs;
   --# derives Last_Position, Last_Valid,
   --#         Ibit_Request from *, Bus.Inputs;
   is
      Word : Bus.Word;

      procedure Get_Coord(I1 : in Bus.Word_Index;
                          I2 : in Bus.Word_Index;
                          Measure : out Measuretypes.Meter)
         --# global in bus.inputs;
         --# derives measure from i1,i2, bus.inputs;
      is
         W1, W2 : Bus.Word;
      begin
         -- Hi word
         Bc1553.Read_Word(Src => Bus_Id,
                          Idx => I1,
                          Subaddress_Idx => 1,
                          Data => W1);
         -- lo word
         Bc1553.Read_Word(Src => Bus_Id,
                          Idx => I2,
                          Subaddress_Idx => 1,
                          Data => W2);
         Measure := Measuretypes.Meter(W2) +
           Measuretypes.meter(W1 * 16#10000#);
      end Get_Coord;
   begin
      -- Check 1T
      if BC1553.Is_Valid(Src => Bus_id,
                         Subaddress_Idx => 1) and then
        BC1553.Is_Fresh(Src => Bus_id,
                        Subaddress_Idx => 1) then
         Get_Coord(I1 => 1, I2 => 2, Measure => Last_Position.X);
         Get_Coord(I1 => 3, I2 => 4, Measure => Last_Position.Y);
         Get_Coord(I1 => 5, I2 => 6, Measure => Last_Position.Z);
         Last_Valid := True;
         -- 1T word 7 - BIT
         BC1553.Read_Word(Src => Bus_id,
                          Idx => 7,
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
   --# global out Last_Position, Last_Valid, Ibit_Request;
   --#        in out Bus.Outputs;
   --# derives Last_Position, Last_Valid, Ibit_Request from &
   --#         Bus.Outputs from *;
   is begin
      Last_Position := Cartesian.Zero_position;
      Last_Valid := False;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => Bus_id,
                               Subaddress_Idx => 1);
   end Init;

   -- Test point
   procedure Command is separate;

end If_Ins;
