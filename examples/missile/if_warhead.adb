-- MCU interface to the warhead, implementation
--
-- $Log: if_warhead.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/11 19:56:52  adi
-- Added get_ibit_state
--
-- Revision 1.1  2003/09/01 18:28:52  adi
-- Initial revision
--
--
with Bc1553, bus;
package body If_Warhead
  --# own State is Last_state, Last_Valid, Ibit_Request;
is
   Last_State   : Stage := Warhead_Cfg.Inactive;
   Last_Valid   : Boolean := False;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   Bus_Id : constant Bc1553.Lru_Name := Bc1553.Warhead;

   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
   end Get_Ibit_State;

   -- Find out the current state and its validity
   procedure Get_stage(Action_stage : out Stage;
                       Valid  : out Boolean)
   --# global in Last_state, Last_Valid;
   --# derives action_stage from Last_state, Last_Valid &
   --#        Valid from Last_Valid;
   is
   begin
      Valid := Last_Valid;
      if Last_Valid then
         Action_Stage := Last_State;
      else
         Action_Stage := Warhead_Cfg.inactive;
      end if;
   end Get_stage;

   -- Command a new stage
   procedure Set_Stage(New_Stage : in Stage)
   is begin
      -- Send it out on 1R at word 1
      BC1553.Write_Word(Data => Warhead_Cfg.State_To_Code(New_Stage),
                        Idx =>  1,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Set_stage;


   -- Kick off a warhead IBIT
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
      -- Send it out on 1R at word 2
      BC1553.Write_Word(Data => Code,
                        Idx =>  2,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Ibit_Start;

   -- Stop a warhead IBIT
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
      -- Send it out on 1R at word 2
      BC1553.Write_Word(Data => Code,
                        Idx =>  2,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Ibit_Stop;

   -- Poll the bus and update states
   procedure Poll
   --# global in out Last_state, Last_Valid, Ibit_Request;
   --#        in Bus.Inputs;
   --# derives Last_state, Last_Valid,
   --#         Ibit_Request from *, Bus.Inputs;
   is
      Word : Bus.Word;
   begin
      -- Check 1T
      if BC1553.Is_Valid(Src => Bus_id,
                         Subaddress_Idx => 1) and then
        BC1553.Is_Fresh(Src => Bus_id,
                        Subaddress_Idx => 1) then
         -- Read the updated stage
         BC1553.Read_Word(Src => Bus_id,
                          Idx => 1,
                          Subaddress_Idx => 1,
                          Data => Word);
         last_State := Warhead_Cfg.Code_To_state(Word);
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
   --# global out Last_state, Last_Valid, Ibit_Request;
   --#        in out Bus.Outputs;
   --# derives Last_state, Last_Valid, Ibit_Request from &
   --#         Bus.Outputs from *;
   is begin
      Last_State := Warhead_Cfg.inactive;
      Last_Valid := False;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => Bus_id,
                               Subaddress_Idx => 1);
   end Init;

   -- Test point
   procedure Command is separate;

end If_Warhead;
