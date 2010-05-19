-- MCU interface to the fuze, implementation
--
-- $Log: if_fuze.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/09/10 21:01:07  adi
-- Added get_ibit_state
--
-- Revision 1.2  2003/08/17 15:30:02  adi
-- Fixed Poll to write out too
--
-- Revision 1.1  2003/08/17 15:11:36  adi
-- Initial revision
--
--
with Bc1553, bus;
package body If_Fuze
  --# own State is Last_state, Last_Valid, Ibit_Request;
is
   Last_State : State_Types.Fuze := State_Types.Unarmed;
   Last_Valid  : Boolean := False;
   Ibit_Request : IBIT.Phase := IBIT.Off;

   Bus_Id : constant Bc1553.Lru_Name := Bc1553.Fuze;

   function Get_Ibit_State return Ibit.Phase
     --# global ibit_request;
   is begin
      return Ibit_Request;
   end Get_Ibit_State;

   -- Find out the current state and its validity
   procedure Get_state(Action_state : out State_Types.fuze;
                       Valid  : out Boolean)
   --# global in Last_state, Last_Valid;
   --# derives action_state from Last_state, Last_Valid &
   --#        Valid from Last_Valid;
   is
   begin
      Valid := Last_Valid;
      if Last_Valid then
         Action_State := Last_State;
      else
         Action_State := State_Types.Unarmed;
      end if;
   end Get_state;

   -- Command an arming
   procedure Arm
     --# global in last_state;
     --#        in out bus.outputs;
     --# derives bus.outputs from *, last_state;
   is begin
      if Last_State = State_Types.Unarmed then
         -- Send it out on 1R at word 1
         BC1553.Write_Word(Data => State_Types.Fuze_Values(State_Types.Arming),
                           Idx =>  1,
                           Subaddress_Idx => 1,
                           Dest => Bus_id);
      end if;
   end Arm;

   -- Command an unarming
   procedure disarm
   is begin
      -- Send it out on 1R at word 1
      BC1553.Write_Word(Data => State_Types.Fuze_Values(State_Types.unarmed),
                        Idx =>  1,
                        Subaddress_Idx => 1,
                        Dest => Bus_id);
   end Disarm;

   -- Kick off a fuze IBIT
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

   -- Stop a fuze IBIT
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
   --#        in Bus.Inputs; in out bus.outputs;
   --# derives Last_state, Last_Valid,
   --#         Ibit_Request from *, Bus.Inputs &
   --# bus.outputs from *, bus.inputs, last_state;
   is
      Word : Bus.Word;
      New_State : State_Types.Fuze;
   begin
      -- Check 1T
      if BC1553.Is_Valid(Src => Bus_id,
                         Subaddress_Idx => 1) and then
        BC1553.Is_Fresh(Src => Bus_id,
                        Subaddress_Idx => 1) then
         -- Read the state
         BC1553.Read_Word(Src => Bus_id,
                          Idx => 1,
                          Subaddress_Idx => 1,
                          Data => Word);
         new_State := State_Types.Fuze_Action(Word);
         -- Deal with the arm/disarm command
         if New_State /= Last_state then
            -- State has switched so turn off the arming/disarming request
            BC1553.Write_Word(Data => 0,
                              Idx =>  1,
                              Subaddress_Idx => 1,
                              Dest => Bus_id);
         end if;
         Last_State := New_State;
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
      Last_State := State_Types.Unarmed;
      Last_Valid := False;
      Ibit_Request := IBIT.Off;
      BC1553.Set_Message_Valid(Dest => Bus_id,
                               Subaddress_Idx => 1);
   end Init;

   -- Test point
   procedure Command is separate;

end If_Fuze;
