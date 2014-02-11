

------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- TcpIp
--
-- Description:
--    Provides the operations to communicate with the SPRE drivers
--    using TCP/IP.
--
------------------------------------------------------------------

package TcpIp is

   MaxMessageLength : constant := 4096;

   subtype MessageLengthT is Integer        range 0 .. MaxMessageLength;
   subtype MessageIndexT  is MessageLengthT range 1 .. MessageLengthT'Last;

   type MessageT is record
      Data   : String(MessageIndexT) := (others => ASCII.Nul);
      Length : MessageLengthT := 0;
   end record;

   NullMsg : constant MessageT := (Data   => (others => ASCII.Nul),
                                   Length => 0);

   --------------------------------------------------------------------
   -- ConnectToSPRE
   --
   -- Description:
   --    Makes a TCP/IP connection to either the Portal port or the Admin
   --    port.
   --
   --------------------------------------------------------------------
   procedure ConnectToSPRE (IsAdmin : in     Boolean;
                            Success :    out Boolean)
     with Global => null;

   --------------------------------------------------------------------
   -- DisconnectFromSPRE
   --
   -- Description:
   --    Closes the TCP/IP connection with either the Portal port or the Admin
   --    port.
   --
   --------------------------------------------------------------------
   procedure DisconnectFromSPRE (IsAdmin : in     Boolean;
                                 Success :    out Boolean)
     with Global => null;

   --------------------------------------------------------------------
   -- OpenAll
   --
   -- Description:
   --    Opens TCP/IP connections to both the Portal and Admin ports.
   --
   --------------------------------------------------------------------
   procedure OpenAll (Success : out Boolean)
     with Global => null;

   --------------------------------------------------------------------
   -- CloseAll
   --
   -- Description:
   --    Closes the TCP/IP connection with both the Portal and Admin ports.
   --
   --------------------------------------------------------------------
   procedure CloseAll
     with Global => null;

   --------------------------------------------------------------------
   -- SendAndReceive
   --
   -- Description:
   --    Sends the Remote Procedure Call (RPC) to SPRE and then attempts to
   --    receive the reply. Success will be false if there is a communication
   --    error.
   --    Outgoing and Incoming do not include the message delineation sequence:
   --    This procedure appends the sequence to the Outgoing string, and
   --    removes it from the Incoming string.
   --
   --------------------------------------------------------------------
   procedure SendAndReceive (IsAdmin  : in     Boolean;
                             Outgoing : in     MessageT;
                             Incoming :    out MessageT;
                             Success  :    out Boolean)
     with Global => null;

   --------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Extracts from the command line any arguments that reset the
   --    default machine name and ports for the Test Devices.
   --
   --------------------------------------------------------------------
   procedure Init (Success  :    out Boolean)
     with Global => null;

end TcpIp;
