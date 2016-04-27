----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

with Ada.Streams,
     System;

use type System.Bit_Order;

with Socket_Timeout,
     Ada.Unchecked_Conversion;

--with Ada.Text_IO;
--use Ada.Text_IO;

package body DNS_Network
  with SPARK_Mode => Off
is
   Server      : Gnat.Sockets.Socket_Type;
   Address     : Gnat.Sockets.Sock_Addr_Type;
   UDP_Socket  : Gnat.Sockets.Socket_Type;
   UDP_Address : Gnat.Sockets.Sock_Addr_Type;

   procedure Initialize_UDP is
   begin
      -- create the socket which will listen for the UDP DNS query
      Gnat.Sockets.Create_Socket
        (Socket => UDP_Socket,
         Family => Gnat.Sockets.Family_Inet,
         Mode   => Gnat.Sockets.Socket_Datagram);

      -- Allow socket to be bound to address already in use
      Gnat.Sockets.Set_Socket_Option
        (UDP_Socket,
         Gnat.Sockets.Socket_Level,
         (Gnat.Sockets.Reuse_Address, True));

      -- bind the socket to the first IP address on localhost, port 53
      -- Address.Addr := Gnat.Sockets.Addresses(
      --   Gnat.Sockets.Get_Host_By_Name(Gnat.Sockets.Host_Name), 1);
      -- bind to any IP address available
      UDP_Address.Addr := Gnat.Sockets.ANY_INET_ADDR;
      UDP_Address.Port := 53;
      Gnat.Sockets.Bind_Socket (UDP_Socket, UDP_Address);
   end Initialize_UDP;

   procedure Initialize_TCP is
   begin
      -- create the socket which will listen for the TCP query
      Gnat.Sockets.Create_Socket
        (Socket => Server,
         Family => Gnat.Sockets.Family_Inet,
         Mode   => Gnat.Sockets.Socket_Stream);

      -- Allow socket to be bound to address already in use
      -- Gnat.Sockets.Set_Socket_Option(Server,
      --   Gnat.Sockets.Socket_Level, (Gnat.Sockets.Reuse_Address, True));
      Address.Addr := Gnat.Sockets.ANY_INET_ADDR;

      -- bind the socket to the first IP address on localhost, port 53
      -- below doesn't work on Linux, as it doesn't resolve host_name correctly
      -- Address.Addr := Gnat.Sockets.Addresses(
      --   Gnat.Sockets.Get_Host_By_Name(Gnat.Sockets.Host_Name), 1);
      Address.Port := 53;
      Gnat.Sockets.Bind_Socket(Server,Address);
      Gnat.Sockets.Listen_Socket(Socket => Server);
   end Initialize_TCP;

   procedure Get_Connection_TCP (Socket : out DNS_Socket) is
      function Convert is new Ada.Unchecked_Conversion
        (DNS_Socket, Socket_Timeout.Socket_Type);
   begin
      Gnat.Sockets.Accept_Socket
        (Server  => Server,
         Socket  => Gnat.Sockets.Socket_Type(Socket),
         Address => Address);
      Socket_Timeout.Set_Socket_Timeout
        (Socket       => Convert (Socket),
         Milliseconds => Socket_Timeout_Milliseconds);
   end Get_Connection_TCP;

   procedure Receive_DNS_Packet_TCP
     (Packet       :    out DNS_Types.DNS_Tcp_Packet;
      Number_Bytes :    out DNS_Types.Packet_Length_Range;
      Socket       : in     DNS_Socket;
      Failure      :    out Boolean)
   is
      use type DNS_Types.Packet_Length_Range;
      use type Ada.streams.Stream_Element_Offset;
      Last_Value : Ada.Streams.Stream_Element_Offset;
      Item       : Ada.Streams.Stream_Element_Array
                     (1 .. DNS_Types.DNS_Packet'Size/8);
      for Item'Address use Packet'Address;
   begin
      Gnat.Sockets.Receive_Socket
        (Socket => Gnat.Sockets.Socket_Type (Socket),
         Item   => Item,
         Last   => Last_Value);
      Number_Bytes := DNS_Types.Packet_Length_Range (Last_Value) - 2;
      if System.Default_Bit_Order=System.Low_Order_First then
         DNS_Types.Byte_Swap (Packet.Rest.Header);
      end if;
      Failure := Number_Bytes < DNS_Types.Packet_Length_Range
                                  (1+DNS_Types.Header_Bits/8) or
                 Number_Bytes > Max_Query_Size;
   exception when others =>
      --Ada.Text_IO.Put_Line ("failure!");
      Failure := True;
   end Receive_DNS_Packet_Tcp;

   -------------------------
   -- Send_DNS_Packet_Tcp --
   -------------------------

   procedure Send_DNS_Packet_Tcp
     (Packet       : in out DNS_Types.DNS_Tcp_Packet;
      Number_Bytes : in     DNS_Types.Packet_Length_Range;
      Socket       : in     DNS_Socket;
      Failure      :    out Boolean)
   is
      use type DNS_Types.Packet_Length_Range;
      use type Ada.Streams.Stream_Element_Offset;
      Response_Stream : Ada.Streams.Stream_Element_Array
                          (1 .. DNS_Types.DNS_Packet'Size/8);
      for Response_Stream'Address use Packet'Address;
      Result_Last : Ada.Streams.Stream_Element_Offset;
   begin
      if System.Default_Bit_Order=System.Low_Order_First then
         DNS_Types.Byte_Swap(Packet.Rest.Header);
      end if;

      Gnat.Sockets.Send_Socket
        (Socket => Gnat.Sockets.Socket_Type (Socket),
         Item   => Response_Stream (1 .. Ada.Streams.Stream_Element_Offset
                                           (Number_Bytes + 2)),
         Last   => Result_Last);
      --Put_Line ("Num bytes sent" &
      --          Ada.Streams.Stream_Element_Offset'Image (Result_Last));
      if Result_Last /= Ada.Streams.Stream_Element_Offset
                          (Number_Bytes + 2)
      then
         Failure := True;
      else
         Failure := False;
      end if;
      Gnat.Sockets.Close_Socket (Gnat.Sockets.Socket_Type (Socket));

   exception when others =>
      Failure := True;
   end Send_DNS_Packet_Tcp;

   procedure Discard_Socket (Socket : in DNS_Socket) is
   begin
      Gnat.Sockets.Close_Socket (Gnat.Sockets.Socket_Type (Socket));
   exception when others =>
      null;
   end Discard_Socket;

   ------------------------
   -- Receive_DNS_Packet --
   ------------------------

   procedure Receive_DNS_Packet
     (Packet        : out DNS_Types.DNS_Packet;
      Number_Bytes  : out DNS_Types.Packet_Length_Range;
      Reply_Address : out Network_Address_and_Port;
      Failure       : out Boolean)
   is
      use type DNS_Types.Packet_Length_Range;
      use type Ada.Streams.Stream_Element_Offset;
      Last_Value : Ada.Streams.Stream_Element_Offset;
      Item       : Ada.Streams.Stream_Element_Array
                     (1 .. DNS_Types.DNS_Packet'Size/8);
      for Item'Address use Packet'Address;
   begin
      Gnat.Sockets.Receive_Socket
        (Socket => UDP_Socket,
         Item   => Item,
         Last   => Last_Value,
         From   => Gnat.Sockets.Sock_Addr_Type (Reply_Address));
      Number_Bytes := DNS_Types.Packet_Length_Range (Last_Value);
      --Put_Line ("Num bytes" &
      --          DNS_Types.Packet_Length_Range'Image (Number_Bytes));
      if System.Default_Bit_Order = System.Low_Order_First then
         DNS_Types.Byte_Swap (Packet.Header);
      end if;
      --Gnat.Sockets.Close_Socket(Socket);
      Failure := False;
   exception when others =>
      Failure := True;
   end Receive_DNS_Packet;

   ---------------------
   -- Send_DNS_Packet --
   ---------------------

   procedure Send_DNS_Packet
     (Packet       : in out DNS_Types.DNS_Packet;
      Number_Bytes : in     DNS_Types.Packet_Length_Range;
      To_Address   : in     Network_Address_and_Port;
      Failure      :    out Boolean)
   is
      use type DNS_Types.Packet_Length_Range;
      use type Ada.streams.Stream_Element_Offset;
      Response_Stream : Ada.Streams.Stream_Element_Array
                          (1 .. DNS_Types.DNS_Packet'Size/8);
      for Response_Stream'Address use Packet'Address;
      Result_Last : Ada.Streams.Stream_Element_Offset;
   begin
      if System.Default_Bit_Order = System.Low_Order_First then
         DNS_Types.Byte_Swap (Packet.Header);
      end if;
      -- connect back to client
      -- Gnat.Sockets.Connect_Socket
      --  (Socket => Reply_UDP_Socket,
      --   Server => Gnat.Sockets.Sock_Addr_Type (To_Address));

      Gnat.Sockets.Send_Socket
        (Socket => UDP_Socket,
         Item   => Response_Stream
                     (1 .. Ada.Streams.Stream_Element_Offset(Number_Bytes)),
         Last   => Result_Last,
         To     => Gnat.Sockets.Sock_Addr_Type (To_Address));
      --Put_Line ("Num bytes" &
      --          Ada.Streams.Stream_Element_Offset'Image (Result_Last));

      if Result_Last /= Ada.Streams.Stream_Element_Offset (Number_Bytes) then
         Failure := True;
      else
         Failure := False;
      end if;

   exception when others =>
      Failure := True;
   end Send_DNS_Packet;

end DNS_Network;
