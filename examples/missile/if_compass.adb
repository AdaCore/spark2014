-- MCU interface to the compass, implementation
--
-- $Log: if_compass.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/09/10 20:18:12  adi
-- Added get_ibit_state
--
-- Revision 1.2  2003/08/08 20:31:18  adi
-- Use of Angle_Ops public child
--
-- Revision 1.1  2003/08/02 19:49:32  adi
-- Initial revision
--
--
--
with Bc1553, Bus, Measuretypes.Angle_Ops;
package body If_Compass
  --# own State is Last_XY, Last_YZ,
  --#    Last_XY_Valid, Last_YZ_Valid, Ibit_Request;
is
   Last_XY, Last_YZ : MeasureTypes.Millirad := MeasureTypes.Angle_zero;
   Last_XY_Valid, Last_YZ_Valid  : Boolean := False;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
   end Get_Ibit_State;

   -- Find out the current XY and its validity
   procedure Get_XY(Angle : out MeasureTypes.Millirad;
                    Valid  : out Boolean)
   --# global in Last_XY, Last_XY_Valid;
   --# derives Angle from Last_XY, Last_XY_Valid &
   --#        Valid from Last_XY_Valid;
   is
   begin
      Valid := Last_XY_Valid;
      if Last_XY_Valid then
         Angle := Last_XY;
      else
         Angle := Measuretypes.Angle_zero;
      end if;
   end Get_XY;

   -- Find out the current YZ and its validity
   procedure Get_YZ(Angle : out MeasureTypes.Millirad;
                    Valid  : out Boolean)
   --# global in Last_YZ, Last_YZ_Valid;
   --# derives Angle from Last_YZ, Last_YZ_Valid &
   --#        Valid from Last_YZ_Valid;
   is
   begin
      Valid := Last_YZ_Valid;
      if Last_YZ_Valid then
         Angle := Last_YZ;
      else
         Angle := Measuretypes.Angle_zero;
      end if;
   end Get_YZ;

   -- Kick off a component IBIT
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
                        Dest => BC1553.Compass);
   end Ibit_Start;

   -- Stop a component IBIT
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
                        Dest => BC1553.Compass);
   end Ibit_Stop;

   -- Poll the bus and update states
   procedure Poll
     --# global in out Last_XY, Last_YZ, Last_XY_Valid,
     --#        Last_YZ_Valid, Ibit_Request;
   --#        in Bus.Inputs;
   --# derives Last_XY, Last_YZ, Last_XY_Valid, Last_YZ_Valid,
   --#         Ibit_Request from *, Bus.Inputs;
   is
      Word : Bus.Word;
   begin
      -- Check 1T
      if BC1553.Is_Valid(Src => Bc1553.Compass,
                         Subaddress_Idx => 1) and then
        BC1553.Is_Fresh(Src => Bc1553.Compass,
                        Subaddress_Idx => 1) then
         -- 1T word 1 - XY angle
         BC1553.Read_Word(Src => BC1553.Compass,
                          Idx => 1,
                          Subaddress_Idx => 1,
                          Data => Word);
         Last_XY := Measuretypes.Angle_Ops.Create_Angle(Word);
         -- And now reading is valid
         Last_XY_Valid := True;
         -- 1T word 2 - YZ angle
         BC1553.Read_Word(Src => BC1553.Compass,
                          Idx => 2,
                          Subaddress_Idx => 1,
                          Data => Word);
         Last_YZ := Measuretypes.Angle_Ops.Create_Angle(Word);
         -- And now reading is valid
         Last_YZ_Valid := True;
         -- 1T word 3 - BIT
         BC1553.Read_Word(Src => BC1553.Compass,
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
     --# global out Last_XY, Last_YZ,
     --#    Last_XY_Valid, Last_YZ_Valid, Ibit_Request;
     --#        in out Bus.Outputs;
     --# derives Last_XY, Last_YZ, Last_XY_Valid,
     --#       Last_YZ_Valid, Ibit_Request from &
     --#         Bus.Outputs from *;
   is begin
      Last_XY := Measuretypes.Angle_zero;
      Last_XY_Valid := False;
      Last_YZ := Measuretypes.Angle_zero;
      Last_YZ_Valid := False;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => BC1553.Compass,
                               Subaddress_Idx => 1);
   end Init;

   -- Test point
   procedure Command is separate;
end If_Compass;
