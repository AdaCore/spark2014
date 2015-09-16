--  Package defining an asbtract interface for the link layer used by
--  the CRTP Communication protocol.
with CRTP_Pack; use CRTP_Pack;

package Link_Interface_Pack is

   --  Procedures and functions

   --  Initialize the selected link layer.
   --  The selected link layer is specified in 'config.ads'.
   procedure Link_Init;

   --  Send a CRTP packet using the link layer specified in
   --  the 'Config' package.
   --  Return 'True' if the packet is correctly sent, 'False'
   --  ortherwise.
   function Link_Send_Packet (Packet : CRTP_Packet) return Boolean;

   --  Receive a CRTP packet using the link layer specified in
   --  the 'Config' package.
   --  Put the task calling it in sleep mode until a packet is received.
   procedure Link_Receive_Packet_Blocking (Packet : out CRTP_Packet);

private

   --  Global variables and constants

   Is_Init : Boolean := False;

end Link_Interface_Pack;
