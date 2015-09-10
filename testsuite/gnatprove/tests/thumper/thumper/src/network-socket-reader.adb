---------------------------------------------------------------------------
-- FILE    : network-socket-reader.adb
-- SUBJECT : Boundary variable package representing the input stream.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(Off);

with Ada.Streams;

package body Network.Socket.Reader is
   use type Ada.Streams.Stream_Element_Offset;
   use type Network.Addresses.Status_Type;

   procedure Receive
     (Message : out Messages.Network_Message;
      From    : out Addresses.UDPv4;
      Status  : out Status_Type) is

      IP_Address         : Addresses.IPv4;
      Address_Status     : Addresses.Status_Type;
      GNAT_Style_Address : GNAT.Sockets.Sock_Addr_Type;
      Elements           : Ada.Streams.Stream_Element_Array(1 .. Message.Data'Length);
      Last               : Ada.Streams.Stream_Element_Offset;
   begin
      Status  := Success;
      Message := (Data => (others => 0), Size => 0);
      -- TODO: Initialize `From` to something sensible in case `Receive` fails.

      GNAT.Sockets.Receive_Socket(Socket, Elements, Last, GNAT_Style_Address);

      -- Convert the received `Ada.Streams.Stream_Element_Array` into a `Network.Octet_Array`.
      for I in Elements'First .. Last loop
         Message.Data(Message.Data'First + Natural(I - Elements'First)) :=
           Network.Octet(Elements(I));
      end loop;
      Message.Size := Natural((Last - Elements'First) + 1);

      -- Convert GNAT address to an IP address.
      -- The address should be valid so conversion shouldn't fail. Check to be sure anyway.
      Addresses.To_IPv4_Address
        (GNAT.Sockets.Image(GNAT_Style_Address.Addr), IP_Address, Address_Status);
      if Address_Status /= Addresses.Success then
         Status := Failure;
      else
         From :=
           Addresses.To_UDPv4_Address(IP_Address, Addresses.Port_Type(GNAT_Style_Address.Port));
      end if;

   exception
      when GNAT.Sockets.Socket_Error =>
         Status := Failure;

      -- If an unexpected exception occurs, just fail.
      when others =>
         Status := Failure;
   end Receive;

end Network.Socket.Reader;
