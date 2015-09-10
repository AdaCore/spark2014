---------------------------------------------------------------------------
-- FILE    : network-socket.adb
-- SUBJECT : Body of a package representing a single socket.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Ada.Exceptions; use Ada.Exceptions;

package body Network.Socket is

   procedure Create_Socket is
   begin
      GNAT.Sockets.Create_Socket
        (Socket, GNAT.Sockets.Family_Inet, GNAT.Sockets.Socket_Datagram);
   exception
      when Ex : others =>
         raise Network_Error with Exception_Message(Ex);
   end Create_Socket;


   procedure Create_And_Bind_Socket(Port : in Addresses.Port_Type) is
   begin
      GNAT.Sockets.Create_Socket
        (Socket, GNAT.Sockets.Family_Inet, GNAT.Sockets.Socket_Datagram);
      GNAT.Sockets.Bind_Socket
        (Socket, (Family => GNAT.Sockets.Family_Inet,
                  Addr   => GNAT.Sockets.Any_Inet_Addr,
                  Port   => GNAT.Sockets.Port_Type(Port)));
   exception
      when Ex : others =>
         raise Network_Error with Exception_Message(Ex);
   end Create_And_Bind_Socket;


   procedure Close is
   begin
      GNAT.Sockets.Close_Socket(Socket);
   end Close;

end Network.Socket;
