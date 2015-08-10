with System; use System;
with Types; use Types;

package FreeRTOS_Pack
  with SPARK_Mode
is
   --  Types
   subtype Pvoid is System.Address;

   --  Constants
   PORT_MAX_DELAY  : constant T_Uint32    := 16#ffffffff#;

   --  Functions and procedures
   function XQueue_Create
     (QueueLength : T_Uint32;
      ItemSize    : T_Uint32) return Pvoid
     with
       Global => null;
   pragma Import (C, XQueue_Create, "w_xQueueCreate");

   function XQueue_Receive
     (XQueue        : Pvoid;
      Buffer        : Pvoid;
      Ticks_To_wait : T_Uint32) return Integer
     with
       Global => null;
   pragma Import (C, XQueue_Receive, "w_xQueueReceive");


   function XQueue_Send
     (XQueue        : Pvoid;
      Item_To_Queue : Pvoid;
      Ticks_To_wait : T_Uint32) return Integer
     with
       Global => null;
   pragma Import (C, XQueue_Send, "w_xQueueSend");


end FreeRTOS_Pack;
