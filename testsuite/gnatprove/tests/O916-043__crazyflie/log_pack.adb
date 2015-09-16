with Ada.Unchecked_Conversion;

package body Log_Pack is

   --  Public procedures and functions

   procedure Log_Init is
   begin
      if Is_Init then
         return;
      end if;

      CRTP_Register_Callback (CRTP_PORT_LOG, Log_CRTP_Handler'Access);

      Is_Init := True;
   end Log_Init;

   function Log_Test return Boolean is
   begin
      return Is_Init;
   end Log_Test;

   procedure Create_Log_Group
     (Name        : String;
      Group_ID    : out Natural;
      Has_Succeed : out Boolean) is
      Log_Groups_Index : constant Natural := Log_Data.Log_Groups_Index;
   begin
      if Log_Groups_Index > Log_Data.Log_Groups'Last or
        Name'Length > MAX_LOG_VARIABLE_NAME_LENGTH
      then
         Has_Succeed := False;
         return;
      end if;

      Log_Data.Log_Groups (Log_Groups_Index).Name :=
        String_To_Log_Name (Name);
      Log_Data.Log_Groups (Log_Groups_Index).Name_Length :=
        Name'Length + 1;
      Group_ID := Log_Groups_Index;
      Log_Data.Log_Groups_Index := Log_Groups_Index + 1;

      Has_Succeed := True;
   end Create_Log_Group;

   procedure Append_Log_Variable_To_Group
     (Group_ID     : Natural;
      Name         : String;
      Log_Type     : Log_Variable_Type;
      Variable     : System.Address;
      Has_Succeed  : out Boolean) is
      Group               : Log_Group;
      Log_Variables_Index : Log_Variable_ID;
   begin
      Has_Succeed := False;

      --  If group ID doesn't exist.
      if Group_ID not in Log_Data.Log_Groups'Range
      then
         return;
      end if;

      Group := Log_Data.Log_Groups (Group_ID);
      Log_Variables_Index := Group.Log_Variables_Index;

      if Log_Variables_Index > Group.Log_Variables'Last or
        Name'Length > MAX_LOG_VARIABLE_NAME_LENGTH
      then
         return;
      end if;

      Group.Log_Variables (Log_Variables_Index).Name :=
        String_To_Log_Name (Name);
      Group.Log_Variables (Log_Variables_Index).Group_ID := Group_ID;
      Group.Log_Variables (Log_Variables_Index).Name_Length := Name'Length + 1;
      Group.Log_Variables (Log_Variables_Index).Log_Type := Log_Type;
      Group.Log_Variables (Log_Variables_Index).Variable := Variable;

      Group.Log_Variables_Index := Log_Variables_Index + 1;

      Log_Data.Log_Groups (Group_ID) := Group;

      Log_Data.Log_Variables (Log_Data.Log_Variables_Count)
        := Log_Data.Log_Groups
          (Group_ID).Log_Variables (Log_Variables_Index)'Access;

      Log_Data.Log_Variables_Count := Log_Data.Log_Variables_Count + 1;
      Has_Succeed := True;
   end Append_Log_Variable_To_Group;

   --  Private procedures and functions

   procedure Log_CRTP_Handler (Packet : CRTP_Packet) is
      function CRTP_Channel_To_Log_Channel is new Ada.Unchecked_Conversion
        (CRTP_Channel, Log_Channel);
      Channel : Log_Channel;
   begin
      Channel := CRTP_Channel_To_Log_Channel (Packet.Channel);

      case Channel is
         when LOG_TOC_CH =>
            Log_TOC_Process (Packet);
         when LOG_CONTROL_CH =>
            Log_Control_Process (Packet);
         when others =>
            null;
      end case;
   end Log_CRTP_Handler;

   procedure Log_TOC_Process (Packet : CRTP_Packet) is
      function T_Uint8_To_Log_TOC_Command is new Ada.Unchecked_Conversion
        (T_Uint8, Log_TOC_Command);
      procedure CRTP_Append_T_Uint8_Data is new CRTP_Append_Data
        (T_Uint8);
      procedure CRTP_Append_T_Uint32_Data is new CRTP_Append_Data
        (T_Uint32);

      Command        : Log_TOC_Command;
      Packet_Handler : CRTP_Packet_Handler;
      Has_Succeed    : Boolean;
      pragma Unreferenced (Has_Succeed);
   begin
      Command := T_Uint8_To_Log_TOC_Command (Packet.Data_1 (1));
      Packet_Handler := CRTP_Create_Packet
        (CRTP_PORT_LOG, Log_Channel'Enum_Rep (LOG_TOC_CH));
      CRTP_Append_T_Uint8_Data
        (Packet_Handler,
         Log_TOC_Command'Enum_Rep (Command),
         Has_Succeed);

      case Command is
         when LOG_CMD_GET_INFO =>
            CRTP_Append_T_Uint8_Data
              (Packet_Handler,
               Log_Data.Log_Variables_Count,
               Has_Succeed);
            --  Add CRC. 0 for the moment..
            CRTP_Append_T_Uint32_Data
              (Packet_Handler,
               0,
               Has_Succeed);
            CRTP_Append_T_Uint8_Data
              (Packet_Handler,
               MAX_LOG_NUMBER_OF_GROUPS,
               Has_Succeed);
            CRTP_Append_T_Uint8_Data
              (Packet_Handler,
               MAX_LOG_NUMBER_OF_GROUPS *
                 MAX_LOG_NUMBER_OF_VARIABLES_PER_GROUP,
               Has_Succeed);

         when LOG_CMD_GET_ITEM =>
            declare
               Var_ID          : constant T_Uint8 := Packet.Data_1 (2);
               Log_Var         : Log_Variable;
               Log_Var_Group   : Log_Group;
            begin
               if Var_ID < Log_Data.Log_Variables_Count then
                  CRTP_Append_T_Uint8_Data
                    (Packet_Handler,
                     Var_ID,
                     Has_Succeed);

                  Log_Var := Log_Data.Log_Variables (Var_ID).all;
                  Log_Var_Group := Log_Data.Log_Groups (Log_Var.Group_ID);
                  CRTP_Append_T_Uint8_Data
                    (Packet_Handler,
                     Log_Variable_Type'Enum_Rep (Log_Var.Log_Type),
                     Has_Succeed);
                  Append_Raw_Data_Variable_Name_To_Packet
                    (Log_Var,
                     Log_Var_Group,
                     Packet_Handler,
                     Has_Succeed);
               end if;
            end;
      end case;
      CRTP_Send_Packet
        (CRTP_Get_Packet_From_Handler (Packet_Handler),
         Has_Succeed);
   end Log_TOC_Process;

   procedure Log_Control_Process (Packet : CRTP_Packet) is
      function T_Uint8_To_Log_Control_Command is new Ada.Unchecked_Conversion
        (T_Uint8, Log_Control_Command);

      Tx_Packet   : CRTP_Packet := Packet;
      Command     : Log_Control_Command;
      Answer      : T_Uint8;
      Has_Succeed : Boolean;
      pragma Unreferenced (Has_Succeed);
   begin
      Command := T_Uint8_To_Log_Control_Command (Packet.Data_1 (1));

      case Command is
         when LOG_CONTROL_CREATE_BLOCK =>
            Answer := Log_Create_Block
              (Block_ID         => Packet.Data_1 (2),
               Ops_Settings_Raw => Packet.Data_1 (3 .. Integer (Packet.Size)));
         when LOG_CONTROL_APPEND_BLOCK =>
            Answer := Log_Append_To_Block
              (Block_ID         => Packet.Data_1 (2),
               Ops_Settings_Raw => Packet.Data_1 (3 .. Integer (Packet.Size)));
         when LOG_CONTROL_DELETE_BLOCK =>
            Answer := Log_Delete_Block (Packet.Data_1 (2));
         when LOG_CONTROL_START_BLOCK =>
            Answer := Log_Start_Block
              (Block_ID => Packet.Data_1 (2),
               Period   => Integer (Packet.Data_1 (3) *  10));
         when LOG_CONTROL_STOP_BLOCK =>
            Answer := Log_Stop_Block (Packet.Data_1 (2));
         when LOG_CONTROL_RESET =>
            Log_Reset;
            Answer := 0;
      end case;

      Tx_Packet.Data_1 (3) := Answer;
      Tx_Packet.Size := 3;
      CRTP_Send_Packet (Tx_Packet, Has_Succeed);
   end Log_Control_Process;

   function Log_Create_Block
     (Block_ID         : T_Uint8;
      Ops_Settings_Raw : T_Uint8_Array) return T_Uint8 is
      Block : access Log_Block;
   begin
      --  Not enough memory to create a new block.
      if Block_ID not in Log_Block_ID then
         return ENOMEM;
      end if;

      Block := Log_Blocks (Block_ID)'Access;
      --  Block with the same ID already exists.
      if not Block.Free then
         return EEXIST;
      end if;

      Block.Free := False;

      return Log_Append_To_Block (Block_ID, Ops_Settings_Raw);
   end Log_Create_Block;

   function Log_Delete_Block (Block_ID : T_Uint8) return T_Uint8 is
      Block     : access Log_Block;
      Cancelled : Boolean;
      pragma Unreferenced (Cancelled);
   begin
      --  Block ID doesn't match anything
      if Block_ID not in Log_Blocks'Range then
         return ENOENT;
      end if;

      Block := Log_Blocks (Block_ID)'Access;

      --  Mark the block as a free one.
      Block.Free := True;
      Block.Variables := null;

      --  Stop the timer.
      Cancel_Handler (Block.Timer, Cancelled);

      return 0;
   end Log_Delete_Block;

   function Log_Append_To_Block
     (Block_ID         : T_Uint8;
      Ops_Settings_Raw : T_Uint8_Array) return T_Uint8 is
      type Ops_Settings_Array is
        array (1 .. Ops_Settings_Raw'Length / 2) of Log_Ops_Setting;
      function T_Uint8_Array_To_Ops_Settings_Array is
        new Ada.Unchecked_Conversion (T_Uint8_Array, Ops_Settings_Array);

      Block        : access Log_Block;
      Ops_Settings : Ops_Settings_Array;
   begin
      --  Block ID doesn't match anything
      if Block_ID not in Log_Blocks'Range then
         return ENOENT;
      end if;

      Block := Log_Blocks (Block_ID)'Access;

      --  Block not created
      if Block.Free then
         return ENOENT;
      end if;

      Ops_Settings := T_Uint8_Array_To_Ops_Settings_Array (Ops_Settings_Raw);

      declare
         function T_Uint8_To_Log_Variable_Type is new Ada.Unchecked_Conversion
           (T_Uint8, Log_Variable_Type);

         Current_Block_Length : T_Uint8;
         Ops_Setting          : Log_Ops_Setting;
         Log_Type             : Log_Variable_Type;
         Variable             : access Log_Variable;
      begin

         for I in Ops_Settings'Range loop
            Current_Block_Length := Calculate_Block_Length (Block);
            Ops_Setting := Ops_Settings (I);

            Log_Type := T_Uint8_To_Log_Variable_Type
              (Ops_Setting.Ops_Type and 16#0F#);

            --  Trying to append a full block
            if Current_Block_Length + Type_Length (Log_Type) >
              CRTP_MAX_DATA_SIZE
            then
               return E2BIG;
            end if;

            --  Trying a to add a variable that does not exist
            if Ops_Setting.ID not in Log_Data.Log_Variables'Range or else
              Log_Data.Log_Variables (Ops_Setting.ID) = null
            then
               return ENOENT;
            end if;

            Variable := Log_Data.Log_Variables (Ops_Setting.ID);

            Append_Log_Variable_To_Block (Block, Variable);
         end loop;
      end;

      return 0;
   end Log_Append_To_Block;

   function Log_Start_Block
     (Block_ID : T_Uint8;
      Period   : Natural) return T_Uint8 is
      Block     : access Log_Block;
      Cancelled : Boolean;
      pragma Unreferenced (Cancelled);
   begin
      --  Block ID doesn't match anything
      if Block_ID not in Log_Blocks'Range then
         return ENOENT;
      end if;

      Block := Log_Blocks (Block_ID)'Access;

      if Period > 0 then
         Cancel_Handler (Block.Timer, Cancelled);
         Block.Timer.Block_ID := Block_ID;
         Block.Timer.Period := Milliseconds (Period);
         Set_Handler (Event   => Block.Timer,
                      At_Time => Clock + Milliseconds (Period),
                      Handler => Log_Block_Timer_Handler);
      else
         --  TODO: single shoot run. Use worker task for it.
         null;
      end if;

      return 0;
   end Log_Start_Block;

   function Log_Stop_Block (Block_ID : T_Uint8) return T_Uint8 is
      Block     : access Log_Block;
      Cancelled : Boolean;
      pragma Unreferenced (Cancelled);
   begin
      --  Block ID doesn't match anything
      if Block_ID not in Log_Blocks'Range then
         return ENOENT;
      end if;

      Block := Log_Blocks (Block_ID)'Access;

      --  Stop the timer.
      Cancel_Handler (Block.Timer, Cancelled);

      return 0;
   end Log_Stop_Block;

   procedure Log_Reset is
      Res   : T_Uint8;
      pragma Unreferenced (Res);
   begin
      if Is_Init then
         for ID in Log_Blocks'Range loop
            Res := Log_Delete_Block (ID);
         end loop;
      end if;
   end Log_Reset;

   procedure Append_Log_Variable_To_Block
     (Block    : access Log_Block;
      Variable : access Log_Variable) is
      Variables_Aux : access Log_Variable := Block.Variables;
   begin
      --  No variables have been appended to this block until now.
      if Variables_Aux = null then
         Block.Variables := Variable;
      else
         while Variables_Aux.Next /= null loop
            Variables_Aux := Variables_Aux.Next;
         end loop;

         Variables_Aux.Next := Variable;
      end if;
   end Append_Log_Variable_To_Block;

   function String_To_Log_Name (Name : String) return Log_Name is
      Result : Log_Name := (others => ASCII.NUL);
   begin
      Result (1 .. Name'Length) := Name;

      return Result;
   end String_To_Log_Name;

   procedure Append_Raw_Data_Variable_Name_To_Packet
     (Variable        : Log_Variable;
      Group           : Log_Group;
      Packet_Handler  : in out CRTP_Packet_Handler;
      Has_Succeed     : out Boolean) is
      subtype Log_Complete_Name is
        String (1 .. Variable.Name_Length + Group.Name_Length);
      subtype Log_Complete_Name_Raw is
        T_Uint8_Array (1 .. Variable.Name_Length + Group.Name_Length);
      function Log_Complete_Name_To_Log_Complete_Name_Raw is new
        Ada.Unchecked_Conversion (Log_Complete_Name, Log_Complete_Name_Raw);
      procedure CRTP_Append_Log_Complete_Name_Raw_Data is new
        CRTP_Append_Data (Log_Complete_Name_Raw);

      Complete_Name     : constant Log_Complete_Name
        := Group.Name (1 .. Group.Name_Length) &
                            Variable.Name (1 .. Variable.Name_Length);
      Complete_Name_Raw : Log_Complete_Name_Raw;
   begin
      Complete_Name_Raw :=
        Log_Complete_Name_To_Log_Complete_Name_Raw (Complete_Name);
      CRTP_Append_Log_Complete_Name_Raw_Data
        (Packet_Handler,
         Complete_Name_Raw,
         Has_Succeed);
   end Append_Raw_Data_Variable_Name_To_Packet;

   function Calculate_Block_Length (Block : access Log_Block) return T_Uint8 is
      Variables    : access Log_Variable := Block.Variables;
      Block_Length : T_Uint8 := 0;
   begin

      while Variables /= null loop
         Block_Length := Block_Length + Type_Length (Variables.Log_Type);
         Variables := Variables.Next;
      end loop;

      return Block_Length;
   end Calculate_Block_Length;

   function Get_Log_Time_Stamp return Log_Time_Stamp is
      subtype  Time_T_Uint8_Array is T_Uint8_Array (1 .. 8);
      function Time_To_Time_T_Uint8_Array is new Ada.Unchecked_Conversion
        (Time, Time_T_Uint8_Array);

      Raw_Time   : Time_T_Uint8_Array;
      Time_Stamp : Log_Time_Stamp;
   begin
      Raw_Time := Time_To_Time_T_Uint8_Array (Clock);

      Time_Stamp := Raw_Time (6 .. 8);

      return Time_Stamp;
   end Get_Log_Time_Stamp;

   --  Tasks and protected objects

   protected body Log_Block_Timing_Event_Handler is

      procedure Log_Run_Block (Event : in out Timing_Event) is
         Block_ID       : constant Log_Block_ID
           := Log_Block_Timing_Event
             (Timing_Event'Class (Event)).Block_ID;
         Period         : constant Time_Span
           := Log_Block_Timing_Event
             (Timing_Event'Class (Event)).Period;
         Variables      : access Log_Variable;
         Time_Stamp     : Log_Time_Stamp;
         Packet_Handler : CRTP_Packet_Handler;
         Has_Succeed    : Boolean;
         pragma Unreferenced (Has_Succeed);

         --  Procedures used to append log data with different types
         procedure CRTP_Append_Log_Time_Stamp_Data is new CRTP_Append_Data
           (Log_Time_Stamp);
         procedure CRTP_Append_T_Uint8_Data is new CRTP_Append_Data
           (T_Uint8);
         procedure CRTP_Append_T_Uint16_Data is new CRTP_Append_Data
           (T_Uint16);
         procedure CRTP_Append_T_Uint32_Data is new CRTP_Append_Data
           (T_Uint32);
         procedure CRTP_Append_T_Int8_Data is new CRTP_Append_Data
           (T_Int8);
         procedure CRTP_Append_T_Int16_Data is new CRTP_Append_Data
           (T_Int16);
         procedure CRTP_Append_T_Int32_Data is new CRTP_Append_Data
           (T_Int32);
         procedure CRTP_Append_Float_Data is new CRTP_Append_Data
           (Float);
      begin
         Time_Stamp := Get_Log_Time_Stamp;

         Packet_Handler :=
           CRTP_Create_Packet (Port    => CRTP_PORT_LOG,
                               Channel => Log_Channel'Enum_Rep (LOG_DATA_CH));

         --  Add block ID to the packet.
         CRTP_Append_T_Uint8_Data (Handler     => Packet_Handler,
                                   Data        => Block_ID,
                                   Has_Succeed => Has_Succeed);
         --  Add a timestamp to the packet
         CRTP_Append_Log_Time_Stamp_Data (Handler     => Packet_Handler,
                                          Data        => Time_Stamp,
                                          Has_Succeed => Has_Succeed);

         Variables := Log_Blocks (Block_ID).Variables;

         --  Add all the variables data in the packet
         while Variables /= null loop
            case Variables.Log_Type is
               when LOG_UINT8 =>
                  declare
                     Value : T_Uint8;
                     for Value'Address use Variables.Variable;
                  begin

                     CRTP_Append_T_Uint8_Data (Handler     => Packet_Handler,
                                               Data        => Value,
                                               Has_Succeed => Has_Succeed);
                  end;
               when LOG_UINT16 =>
                  declare
                     Value : T_Uint16;
                     for Value'Address use Variables.Variable;
                  begin

                     CRTP_Append_T_Uint16_Data (Handler     => Packet_Handler,
                                               Data        => Value,
                                               Has_Succeed => Has_Succeed);
                  end;
               when LOG_UINT32 =>
                  declare
                     Value : T_Uint32;
                     for Value'Address use Variables.Variable;
                  begin

                     CRTP_Append_T_Uint32_Data (Handler     => Packet_Handler,
                                               Data        => Value,
                                               Has_Succeed => Has_Succeed);
                  end;
               when LOG_INT8 =>
                  declare
                     Value : T_Int8;
                     for Value'Address use Variables.Variable;
                  begin

                     CRTP_Append_T_Int8_Data (Handler     => Packet_Handler,
                                               Data        => Value,
                                               Has_Succeed => Has_Succeed);
                  end;
               when LOG_INT16 =>
                  declare
                     Value : T_Int16;
                     for Value'Address use Variables.Variable;
                  begin

                     CRTP_Append_T_Int16_Data (Handler     => Packet_Handler,
                                               Data        => Value,
                                               Has_Succeed => Has_Succeed);
                  end;
               when LOG_INT32 =>
                  declare
                     Value : T_Int32;
                     for Value'Address use Variables.Variable;
                  begin

                     CRTP_Append_T_Int32_Data (Handler     => Packet_Handler,
                                               Data        => Value,
                                               Has_Succeed => Has_Succeed);
                  end;
               when LOG_FLOAT =>
                  declare
                     Value : Float;
                     for Value'Address use Variables.Variable;
                  begin

                     CRTP_Append_Float_Data (Handler     => Packet_Handler,
                                             Data        => Value,
                                             Has_Succeed => Has_Succeed);
                  end;
            end case;

            Variables := Variables.Next;
         end loop;

         if not CRTP_Is_Connected then
            Log_Reset;
            CRTP_Reset;
         else
            CRTP_Send_Packet
              (Packet       => CRTP_Get_Packet_From_Handler (Packet_Handler),
               Has_Succeed  => Has_Succeed);
         end if;

         Set_Handler (Event   => Event,
                      At_Time => Clock + Period,
                      Handler => Log_Block_Timer_Handler);
      end Log_Run_Block;

   end Log_Block_Timing_Event_Handler;

end Log_Pack;
