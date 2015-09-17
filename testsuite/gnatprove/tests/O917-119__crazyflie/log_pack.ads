pragma SPARK_Mode (On);

with System;
with Ada.Real_Time; use Ada.Real_Time;
with Ada.Real_Time.Timing_Events; use Ada.Real_Time.Timing_Events;

with CRTP_Pack; use CRTP_Pack;
with Types; use Types;

package Log_Pack with SPARK_Mode
is
   --  Types

   --  Type representing all the variable types we can log.
   type Log_Variable_Type is
     (LOG_UINT8,
      LOG_UINT16,
      LOG_UINT32,
      LOG_INT8,
      LOG_INT16,
      LOG_INT32,
      LOG_FLOAT);
   for Log_Variable_Type use
     (LOG_UINT8  => 1,
      LOG_UINT16 => 2,
      LOG_UINT32 => 3,
      LOG_INT8   => 4,
      LOG_INT16  => 5,
      LOG_INT32  => 6,
      LOG_FLOAT  => 7);
   for Log_Variable_Type'Size use 8;

   --  Type representing all the avalaible log module CRTP channels.
   type Log_Channel is
     (LOG_TOC_CH,
      LOG_CONTROL_CH,
      LOG_DATA_CH);
   for Log_Channel use
     (LOG_TOC_CH      => 0,
      LOG_CONTROL_CH  => 1,
      LOG_DATA_CH     => 2);
   for Log_Channel'Size use 2;

   --  Type reprensenting all the log commands.
   --  LOG_CMD_GET_INFO is requested at connexion to fetch the TOC.
   --  LOG_CMD_GET_ITEM is requested whenever the client wants to
   --  fetch the newest variable data.
   type Log_TOC_Command is
     (LOG_CMD_GET_ITEM,
      LOG_CMD_GET_INFO);
   for Log_TOC_Command use
     (LOG_CMD_GET_ITEM => 0,
      LOG_CMD_GET_INFO => 1);
   for Log_TOC_Command'Size use 8;

   --  Type representing all the available log control commands.
   type Log_Control_Command is
     (LOG_CONTROL_CREATE_BLOCK,
      LOG_CONTROL_APPEND_BLOCK,
      LOG_CONTROL_DELETE_BLOCK,
      LOG_CONTROL_START_BLOCK,
      LOG_CONTROL_STOP_BLOCK,
      LOG_CONTROL_RESET);
   for Log_Control_Command use
     (LOG_CONTROL_CREATE_BLOCK => 0,
      LOG_CONTROL_APPEND_BLOCK => 1,
      LOG_CONTROL_DELETE_BLOCK => 2,
      LOG_CONTROL_START_BLOCK  => 3,
      LOG_CONTROL_STOP_BLOCK   => 4,
      LOG_CONTROL_RESET        => 5);
   for Log_Control_Command'Size use 8;

   type Log_Block is limited private;

   --  Global variables and constants

   --  Constant array registering the length of each log variable type
   --  in Bytes.
   Type_Length : array (Log_Variable_Type) of T_Uint8
     := (LOG_UINT8  => 1,
         LOG_UINT16 => 2,
         LOG_UINT32 => 4,
         LOG_INT8   => 1,
         LOG_INT16  => 2,
         LOG_INT32  => 4,
         LOG_FLOAT  => 4);

   --  Error code constants
   ENOENT : constant := 2;
   E2BIG  : constant := 7;
   ENOMEM : constant := 12;
   EEXIST : constant := 17;

   --  Limitation of the variable/group name size.
   MAX_LOG_VARIABLE_NAME_LENGTH : constant := 14;

   --  Maximum number of groups we can create.
   MAX_LOG_NUMBER_OF_GROUPS              : constant := 20;
   --  Maximum number of variables we can create inside a group.
   MAX_LOG_NUMBER_OF_VARIABLES_PER_GROUP : constant := 8;
   --  Maximum number of variables we can log at the same time.
   MAX_LOG_OPS                           : constant := 64;
   --  Maximum number of blocks we can create.
   MAX_LOG_BLOCKS                        : constant := 8;

   --  Procedures and functions

   --  Initialize the log subsystem.
   procedure Log_Init;

   --  Test if the log subsystem is initialized.
   function Log_Test return Boolean;

   --  Create a log group if there is any space left and if the name
   --  is not too long.
   procedure Create_Log_Group
     (Name        : String;
      Group_ID    : out Natural;
      Has_Succeed : out Boolean);

   --  Append a variable to a log group.
   procedure Append_Log_Variable_To_Group
     (Group_ID     : Natural;
      Name         : String;
      Log_Type     : Log_Variable_Type;
      Variable     : System.Address;
      Has_Succeed  : out Boolean);

private

   --  Types

   subtype Log_Name is String (1 .. MAX_LOG_VARIABLE_NAME_LENGTH);

   --  Type representing a log variable. Log variables
   --  can be chained together inside a same block.
   type Log_Variable is record
      Group_ID     : Natural;
      Name         : Log_Name;
      Name_Length  : Natural;
      Log_Type     : Log_Variable_Type;
      Variable     : System.Address := System.Null_Address;
      Next         : access Log_Variable := null;
   end record;

   subtype Log_Group_ID is T_Uint8 range
     0 .. MAX_LOG_NUMBER_OF_VARIABLES_PER_GROUP - 1;

   type Log_Group_Variable_Array is
     array (Log_Group_ID) of aliased Log_Variable;

   subtype Log_Variable_ID is T_Uint8 range
     0 .. MAX_LOG_NUMBER_OF_VARIABLES_PER_GROUP * MAX_LOG_NUMBER_OF_GROUPS - 1;

   type Log_Variable_Array is array (Log_Variable_ID) of access Log_Variable;

   --  Type representing a log group.
   --  Log groups can contain several log variables.
   type Log_Group is record
      Name                : Log_Name;
      Name_Length         : Natural;
      Log_Variables       : Log_Group_Variable_Array;
      Log_Variables_Index : Log_Variable_ID := 0;
   end record;

   type Log_Group_Array is
     array (0 .. MAX_LOG_NUMBER_OF_GROUPS - 1) of Log_Group;

   --  Type repesentic the log TOC
   type Log_TOC is record
      Log_Groups          : Log_Group_Array;
      Log_Variables       : Log_Variable_Array := (others => null);
      Log_Groups_Index    : Natural := 0;
      Log_Variables_Count : T_Uint8 := 0;
   end record;

   type Log_Ops_Setting is record
      Ops_Type     : T_Uint8;
      ID           : T_Uint8;
   end record;
   for Log_Ops_Setting'Size use 16;

   subtype Log_Block_ID is T_Uint8 range 1 .. MAX_LOG_BLOCKS;

   --  Extension of the Timing_Event tagged type to store an
   --  additional attribute : the block to log.
   type Log_Block_Timing_Event is new Timing_Event with record
      Block_ID : Log_Block_ID;
      Period   : Time_Span;
   end record;

   --  Type representing a log block. A log block sends all
   --  its variables data every time the Timing_Event timer expires.
   type Log_Block is record
      ID        : Log_Block_ID;
      Free      : Boolean := True;
      Timer     : Log_Block_Timing_Event;
      Variables : access Log_Variable := null;
   end record;

   --  Type used to encode timestamps when dending log data.
   subtype Log_Time_Stamp is T_Uint8_Array (1 .. 3);

   --  Tasks and protected objects

   protected Log_Block_Timing_Event_Handler is
      pragma Interrupt_Priority;

      procedure Log_Run_Block (Event : in out Timing_Event)
        with Extensions_Visible;
   end Log_Block_Timing_Event_Handler;

   --  Global variables and constants

   Log_Block_Timer_Handler : constant Timing_Event_Handler
     := Log_Block_Timing_Event_Handler.Log_Run_Block'Access;

   Is_Init : Boolean := False;

   --  Log TOC
   Log_Data : aliased Log_TOC;

   --  Log blocks
   Log_Blocks : array (Log_Block_ID) of aliased Log_Block;

   --  Procedures and functions

   --  Handler called when a CRTP packet is received in the log
   --  port.
   procedure Log_CRTP_Handler (Packet : CRTP_Packet);

   --  Process a command related to TOC demands from the python client.
   procedure Log_TOC_Process (Packet : CRTP_Packet);

   --  Process a command related to log control.
   procedure Log_Control_Process (Packet : CRTP_Packet);

   --  Create a log block, contatining all the variables specified
   --  in Ops_Settings parameter.
   function Log_Create_Block
     (Block_ID         : T_Uint8;
      Ops_Settings_Raw : T_Uint8_Array) return T_Uint8;

   --  Delete the specified block.
   function Log_Delete_Block (Block_ID : T_Uint8) return T_Uint8;

   --  Append the variables specified in Ops_Settings to the
   --  block identified with Block_ID.
   function Log_Append_To_Block
     (Block_ID         : T_Uint8;
      Ops_Settings_Raw : T_Uint8_Array) return T_Uint8;

   --  Start logging the specified block at each period (in ms).
   function Log_Start_Block
     (Block_ID : T_Uint8;
      Period   : Natural) return T_Uint8;

   --  Stop logging the specified block.
   function Log_Stop_Block (Block_ID : T_Uint8) return T_Uint8;

   --  Delete all the log blocks.
   procedure Log_Reset;

   --  Append a log vraible to the specified block.
   procedure Append_Log_Variable_To_Block
     (Block    : access Log_Block;
      Variable : access Log_Variable);
   pragma Inline (Append_Log_Variable_To_Block);

   --  Convert an unbounded string to a Log_Name, with a fixed size.
   function String_To_Log_Name (Name : String) return Log_Name;
   pragma Inline (String_To_Log_Name);

   --  Calculate the current block legnth, to ensure that it will fit in
   --  a single CRTP packet.
   function Calculate_Block_Length (Block : access Log_Block) return T_Uint8;
   pragma Inline (Calculate_Block_Length);

   --  Get a log timestamp from the current clock tick count.
   function Get_Log_Time_Stamp return Log_Time_Stamp;
   pragma Inline (Get_Log_Time_Stamp);

   --  Append raw data from the variable and group name.
   procedure Append_Raw_Data_Variable_Name_To_Packet
     (Variable       : Log_Variable;
      Group          : Log_Group;
      Packet_Handler : in out CRTP_Packet_Handler;
      Has_Succeed    : out Boolean);

end Log_Pack;
