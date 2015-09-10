---------------------------------------------------------------------------
-- FILE    : network-socket.ads
-- SUBJECT : Specification of a package representing a single socket.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- This non-SPARK package encapsulates the initialization and finalization of vendor's sockets
-- library so clients are not aware of which underlying library is used. Exceptions raised by
-- the underlying library are translated into vendor neutral exceptions.
--
-- This package also provides a simplified, easier to use interface exposing the abstraction of
-- a single UDP socket (either client or server).
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Network.Addresses;
private with GNAT.Sockets;

package Network.Socket is

   -- A general purpose exception used for all kinds of network problems.
   Network_Error : exception;

   -- This procedure creates the socket without binding it to a specified port.
   -- It is useful for clients.
   procedure Create_Socket;

   -- This procedure creates a socket and binds it to the specified port.
   -- It is useful for servers.
   procedure Create_And_Bind_Socket(Port : in Addresses.Port_Type);

   -- This procedure closes the socket. After being closed the socket should not be used.
   procedure Close;

private
   -- A single global socket.
   -- This is here so it can be accessed by child packages.
   Socket : GNAT.Sockets.Socket_Type;

end Network.Socket;
