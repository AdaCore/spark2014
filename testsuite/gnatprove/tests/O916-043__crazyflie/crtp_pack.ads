with System;
with Ada.Real_Time; use Ada.Real_Time;

with Generic_Queue_Pack;
with Types; use Types;
with Config; use Config;

pragma Elaborate_All (Generic_Queue_Pack);

package CRTP_Pack is

   --  Constants

   CRTP_MAX_DATA_SIZE : constant := 30;
   CRTP_TX_QUEUE_SIZE : constant := 60;
   CRTP_RX_QUEUE_SIZE : constant := 2;
   CRTP_NBR_OF_PORTS  : constant := 16;

   --  Types

   --  Type used for representing a CRTP channel, which can be seen
   --  as a sub-set for a specific port.
   type CRTP_Channel is new T_Uint8 range 0 .. 3;
   for CRTP_Channel'Size use 2;

   --  Enumeration type for CRTP ports. Each port corresponds to
   --  a specific modules.
   type CRTP_Port is (CRTP_PORT_CONSOLE,
                      CRTP_PORT_PARAM,
                      CRTP_PORT_COMMANDER,
                      CRTP_PORT_MEM,
                      CRTP_PORT_LOG,
                      CRTP_PORT_PLATFORM,
                      CRTP_PORT_LINK);
   for CRTP_Port use (CRTP_PORT_CONSOLE   => 16#00#,
                      CRTP_PORT_PARAM     => 16#02#,
                      CRTP_PORT_COMMANDER => 16#03#,
                      CRTP_PORT_MEM       => 16#04#,
                      CRTP_PORT_LOG       => 16#05#,
                      CRTP_PORT_PLATFORM  => 16#0D#,
                      CRTP_PORT_LINK      => 16#0F#);
   for CRTP_Port'Size use 4;

   --  Type for representing the two reserved bits in a CRTP packet.
   --  These bits are used for the transport layer.
   type CRTP_Reserved is new T_Uint8 range 0 .. 3;
   for CRTP_Reserved'Size use 2;

   --  Type for CRTP packet data.
   subtype CRTP_Data is T_Uint8_Array (1 .. CRTP_MAX_DATA_SIZE);

   --  Type used to represenet a raw CRTP Packet (Header + Data).
   type CRTP_Raw is array (1 .. CRTP_MAX_DATA_SIZE + 1) of T_Uint8;

   --  Type listing the different representations for the union type
   --  CRTP Packet.
   type Crpt_Packet_Representation is (DETAILED, HEADER_DATA, RAW);

   --  Type for CRTP packets.
   type CRTP_Packet (Repr : Crpt_Packet_Representation := DETAILED) is record
      Size     : T_Uint8;

      case Repr is
         when DETAILED =>
            Channel    : CRTP_Channel;
            Reserved   : CRTP_Reserved;
            Port       : CRTP_Port;
            Data_1     : CRTP_Data;
         when HEADER_DATA =>
            Header     : T_Uint8;
            Data_2     : CRTP_Data;
         when RAW =>
            Raw        : CRTP_Raw;
      end case;
   end record;

   pragma Unchecked_Union (CRTP_Packet);
   for CRTP_Packet'Size use 256;
   pragma Pack (CRTP_Packet);

   --  Type used to easily manipulate CRTP packet.
   type CRTP_Packet_Handler is private;

   --  Procedures and functions

   --  Create a CRTP Packet handler to append/get data.
   function CRTP_Create_Packet
     (Port    : CRTP_Port;
      Channel : CRTP_Channel) return CRTP_Packet_Handler;

   --  Return an handler to easily manipulate the CRTP packet.
   function CRTP_Get_Handler_From_Packet
     (Packet : CRTP_Packet) return CRTP_Packet_Handler;

   --  Return the CRTP Packet contained in the CRTP Packet handler.
   function CRTP_Get_Packet_From_Handler
     (Handler : CRTP_Packet_Handler) return CRTP_Packet;

   --  Append data to the CRTP Packet.
   generic
      type T_Data is private;
   procedure CRTP_Append_Data
     (Handler        : in out CRTP_Packet_Handler;
      Data           : T_Data;
      Has_Succeed    : out Boolean);

   --  Get data at a specified index of the CRTP Packet data field.
   generic
      type T_Data is private;
   procedure CRTP_Get_Data
     (Handler    : CRTP_Packet_Handler;
      Index      : Integer;
      Data       : out T_Data;
      Has_Succeed : out Boolean);

   --  Function pointer type for callbacks.
   type CRTP_Callback is access procedure (Packet : CRTP_Packet);

   --  Reset the index, the size and the data contained in the handler.
   procedure CRTP_Reset_Handler (Handler : in out CRTP_Packet_Handler);

   --  Get the size of the CRTP packet contained in the handler.
   function CRTP_Get_Packet_Size
     (Handler : CRTP_Packet_Handler) return T_Uint8;

   --  Receive a packet from the port queue, putting the task calling it
   --  in sleep mode while a packet has not been received
   procedure CRTP_Receive_Packet_Blocking
     (Packet           : out CRTP_Packet;
      Port_ID          : CRTP_Port);

   --  Send a packet, with a given Timeout
   procedure CRTP_Send_Packet
     (Packet : CRTP_Packet;
      Has_Succeed : out Boolean;
      Time_To_Wait : Time_Span := Milliseconds (0));

   --  Register a callback to be called when a packet is received in
   --  the port queue
   procedure CRTP_Register_Callback
     (Port_ID  : CRTP_Port;
      Callback : CRTP_Callback);

   --  Unregister the callback for this port.
   procedure CRTP_Unregister_Callback (Port_ID : CRTP_Port);

   --  Reset the CRTP module by flushing the Tx Queue.
   procedure CRTP_Reset;

   --  Used by the Commander module to state if we are still connected or not.
   procedure CRTP_Set_Is_Connected (Value : Boolean);

   --  Used to know if we are still connected.
   function CRTP_Is_Connected return Boolean;

private
   Bla : CRTP_Packet;
   package CRTP_Queue is new Generic_Queue_Pack (CRTP_Packet, Bla);

   --  Types
   type CRTP_Packet_Handler is record
      Packet : CRTP_Packet;
      Index  : Positive;
   end record;

   --  Tasks and protected objects

   --  Protected object queue for transmission.
   Tx_Queue : CRTP_Queue.Protected_Queue
     (System.Interrupt_Priority'Last, CRTP_TX_QUEUE_SIZE);

   --  Protected object queue for reception.
   Rx_Queue : CRTP_Queue.Protected_Queue
     (System.Interrupt_Priority'Last, CRTP_RX_QUEUE_SIZE);

   --  Array of protected object queues, one for each task.
   Port_Queues : array (CRTP_Port) of CRTP_Queue.Protected_Queue
     (System.Interrupt_Priority'Last, 1);

   --  Array of callbacks when a packet is received.
   Callbacks : array (CRTP_Port) of CRTP_Callback := (others => null);

   --  Task in charge of transmitting the messages in the Tx Queue
   --  to the link layer.
   task CRTP_Tx_Task is
      pragma Priority (CRTP_RXTX_TASK_PRIORITY);
   end CRTP_Tx_Task;

   --  Task in charge of dequeuing the messages in teh Rx_queue
   --  to put them in the Port_Queues.
   task CRTP_Rx_Task is
      pragma Priority (CRTP_RXTX_TASK_PRIORITY);
   end CRTP_Rx_Task;

   --  Global variables

   --  Number of dropped packets.
   Dropped_Packets : Natural := 0;
   --  Used to know if we are still connected or not.
   Is_Connected    : Boolean := False;

end CRTP_Pack;
