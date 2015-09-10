---------------------------------------------------------------------------
-- FILE    : network-socket-writer.adb
-- SUBJECT : Boundary variable package representing the output stream.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(Off);

with Ada.Streams;

package body Network.Socket.Writer is
   use type Ada.Streams.Stream_Element_Offset;

   procedure Send
     (Message : in  Messages.Network_Message;
      To      : in  Addresses.UDPv4;
      Status  : out Status_Type) is

      IP_String          : String(1 .. 15);
      IP_String_Size     : Natural;
      GNAT_Style_Address : GNAT.Sockets.Sock_Addr_Type;
      Elements           : Ada.Streams.Stream_Element_Array(1 .. Message.Data'Length);
      Last               : Ada.Streams.Stream_Element_Offset;
   begin
      Status := Success;

      -- Convert the incoming IP address to GNAT style.
      Addresses.To_IPv4_String(Addresses.Get_IPv4(To), IP_String, IP_String_Size);
      GNAT_Style_Address.Addr := GNAT.Sockets.Inet_Addr(IP_String(1 .. IP_String_Size));
      GNAT_Style_Address.Port := GNAT.Sockets.Port_Type(Addresses.Get_Port(To));

      -- Covert the incoming Network.Octet_Array to an Ada.Streams.Stream_Element_Array.
      Elements := (others => 0);
      for I in Message.Data'First .. Message.Size loop
         Elements(Elements'First  + Ada.Streams.Stream_Element_Offset(I - Message.Data'First)) :=
           Ada.Streams.Stream_Element(Message.Data(I));
      end loop;

      -- Send the datagram.
      GNAT.Sockets.Send_Socket
        (Socket,
         Elements(Elements'First .. (Elements'First + Ada.Streams.Stream_Element_Offset(Message.Size) - 1)),
         Last,
         GNAT_Style_Address);

      -- Check if the entire datagram was sent.
      if Last /= Elements'First + Ada.Streams.Stream_Element_Offset(Message.Size) - 1 then
         Status := Failure;
      end if;
   exception
      when GNAT.Sockets.Socket_Error =>
         Status := Failure;

      -- If an unexpected exception occurs, just fail.
      when others =>
         Status := Failure;
   end Send;

end Network.Socket.Writer;
