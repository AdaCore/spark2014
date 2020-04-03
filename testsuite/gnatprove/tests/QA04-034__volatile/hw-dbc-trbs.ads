--
-- Copyright (C) 2016-2017 secunet Security Networks AG
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--

private package HW.DbC.TRBs is

   TRB_Size : constant := 16;

   type T is record
      Parameter : Word64;
      Status    : Word32;
      Control   : Word32;
   end record
   with
      Pack,
      Volatile,
      Alignment => Natural'Max (16, TRB_Size);

   ----------------------------------------------------------------------------

   TRBs_Per_Ring : constant := 2 ** 6;
   Ring_Size     : constant := TRBs_Per_Ring * TRB_Size;
   type Ring_Range is mod TRBs_Per_Ring;

   type Transfer_Ring is array (Ring_Range) of T
   with
      Pack,
      Volatile,
      Alignment => Ring_Size;
   --  Use size for alignment:
   --  It always fullfills page crossing requirements.

   ----------------------------------------------------------------------------

   type Transfer_Type is mod 2 ** 2;
   No_Data_Stage                       : constant Transfer_Type := 0;
   OUT_Data_Stage                      : constant Transfer_Type := 2;
   IN_Data_Stage                       : constant Transfer_Type := 3;

   type Direction is mod 2 ** 1;
   Dir_OUT                             : constant Direction := 0;
   Dir_IN                              : constant Direction := 1;

   type TRB_Types is mod 2 ** 6;
   Empty                               : constant TRB_Types := 0;
   Normal                              : constant TRB_Types := 1;
   Setup_Stage                         : constant TRB_Types := 2;
   Data_Stage                          : constant TRB_Types := 3;
   Status_Stage                        : constant TRB_Types := 4;
   Isoch                               : constant TRB_Types := 5;
   Link                                : constant TRB_Types := 6;
   Event_Data                          : constant TRB_Types := 7;
   NoOp                                : constant TRB_Types := 8;
   Enable_Slot_Command                 : constant TRB_Types := 9;
   Disable_Slot_Command                : constant TRB_Types := 10;
   Address_Device_Command              : constant TRB_Types := 11;
   Configure_Endpoint_Command          : constant TRB_Types := 12;
   Evaluate_Context_Command            : constant TRB_Types := 13;
   Reset_Endpoint_Command              : constant TRB_Types := 14;
   Stop_Endpoint_Command               : constant TRB_Types := 15;
   Set_TR_Dequeue_Pointer_Command      : constant TRB_Types := 16;
   Reset_Device_Command                : constant TRB_Types := 17;
   Force_Event_Command                 : constant TRB_Types := 18;
   Negotiate_Bandwidth_Command         : constant TRB_Types := 19;
   Set_Latency_Tolerance_Value_Command : constant TRB_Types := 20;
   Get_Port_Bandwidth_Command          : constant TRB_Types := 21;
   Force_Header_Command                : constant TRB_Types := 22;
   NoOp_Command                        : constant TRB_Types := 23;
   Transfer_Event                      : constant TRB_Types := 32;
   Command_Completion_Event            : constant TRB_Types := 33;
   Port_Status_Change_Event            : constant TRB_Types := 34;
   Bandwidth_Request_Event             : constant TRB_Types := 35;
   Doorbell_Event                      : constant TRB_Types := 36;
   Host_Controller_Event               : constant TRB_Types := 37;
   Device_Notification_Event           : constant TRB_Types := 38;
   MFINDEX_Wrap_Event                  : constant TRB_Types := 39;
   NEC_Firmware_Request_Event          : constant TRB_Types := 48;
   NEC_Firmware_Request_Command        : constant TRB_Types := 49;

   type Completion_Code is mod 2 ** 8;
   Invalid                          : constant Completion_Code := 0;
   Success                          : constant Completion_Code := 1;
   Data_Buffer_Error                : constant Completion_Code := 2;
   Babble_Detected_Error            : constant Completion_Code := 3;
   USB_Transaction_Error            : constant Completion_Code := 4;
   TRB_Error                        : constant Completion_Code := 5;
   Stall_Error                      : constant Completion_Code := 6;
   Resource_Error                   : constant Completion_Code := 7;
   Bandwidth_Error                  : constant Completion_Code := 8;
   No_Slots_Available_Error         : constant Completion_Code := 9;
   Invalid_Stream_Type_Error        : constant Completion_Code := 10;
   Slot_Not_Enabled_Error           : constant Completion_Code := 11;
   Endpoint_Not_Enabled_Error       : constant Completion_Code := 12;
   Short_Packet                     : constant Completion_Code := 13;
   Ring_Underrun                    : constant Completion_Code := 14;
   Ring_Overrun                     : constant Completion_Code := 15;
   VF_Event_Ring_Full_Error         : constant Completion_Code := 16;
   Parameter_Error                  : constant Completion_Code := 17;
   Bandwidth_Overrun_Error          : constant Completion_Code := 18;
   Context_State_Error              : constant Completion_Code := 19;
   No_Ping_Response_Error           : constant Completion_Code := 20;
   Event_Ring_Full_Error            : constant Completion_Code := 21;
   Incompatible_Device_Error        : constant Completion_Code := 22;
   Missed_Service_Error             : constant Completion_Code := 23;
   Command_Ring_Stopped             : constant Completion_Code := 24;
   Command_Aborted                  : constant Completion_Code := 25;
   Stopped                          : constant Completion_Code := 26;
   Stopped_Length_Invalid           : constant Completion_Code := 27;
   Max_Exit_Latency_Too_Large_Error : constant Completion_Code := 29;
   Isoch_Buffer_Overrun             : constant Completion_Code := 31;
   Event_Lost_Error                 : constant Completion_Code := 32;
   Undefined_Error                  : constant Completion_Code := 33;
   Invalid_Stream_ID_Error          : constant Completion_Code := 34;
   Secondary_Bandwidth_Error        : constant Completion_Code := 35;
   Split_Transaction_Error          : constant Completion_Code := 36;
   function CC_To_Usb_Error (CC : Completion_Code) return Error;

   ----------------------------------------------------------------------------

   procedure Set_Length (Data : in out T; Length : in Natural);
   function Get_Event_Length (Data : T) return Natural
   with Volatile_Function;

   function Get_Completion_Code (Data : T) return Completion_Code
   with Volatile_Function;

   procedure Set_Cycle (Data : in out T; Cycle : in Bit);
   function Get_Cycle (Data : T) return Bit
   with Volatile_Function;
   procedure Set_ISP (Data : in out T);
   procedure Set_IOC (Data : in out T);

   procedure Set_Type (Data : in out T; TRB_Type : in TRB_Types);
   function Get_Type (Data : T) return TRB_Types
   with Volatile_Function;

   function Get_Endpoint_ID (Data : T) return Natural
   with Volatile_Function;
   function Get_Slot_ID (Data : T) return Word8
   with Volatile_Function;

   procedure Set_Parameter (Data : in out T; Parameter : Word64);
   function Get_Parameter (Data : T) return Word64
   with Volatile_Function;

   procedure Clear (TR : out T; PCS : in Bit);
   procedure Clear_Ring (TR : out Transfer_Ring; PCS : in Bit);
   procedure Init_Cycle_Ring
     (Ring     :    out Transfer_Ring;
      Physical : in     Word64);

end HW.DbC.TRBs;

--  vim: set ts=8 sts=3 sw=3 et:
