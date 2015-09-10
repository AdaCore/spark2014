---------------------------------------------------------------------------
-- FILE    : thumper_server.adb
-- SUBJECT : Main procedure of the Thumper server.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- This procedure initializes various global items and then calls the SPARK procedure
-- Service_Clients.
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Ada.Exceptions;
with Ada.Strings.Unbounded;
with Ada.Text_IO;

with Cryptographic_Services;
with Data_Storage;
with Network.Addresses;
with Network.Socket;
--with Remote_Access;
with Server_SPARK_Boundary;
with Thumper_Switches;

use Ada.Exceptions;
use Ada.Strings.Unbounded;
use Thumper_Switches;

procedure Thumper_Server is
   use type Cryptographic_Services.Status_Type;

   Command_Line_Okay : Boolean;
   Error_Message : Unbounded_String;
   Crypto_Status : Cryptographic_Services.Status_Type;
begin
   -- Be sure the command line makes sense.
   Thumper_Switches.Validate(Thumper_Switches.Server, Command_Line_Okay, Error_Message);
   if not Command_Line_Okay then
      Ada.Text_IO.Put_Line("*** Command line error: " & To_String(Error_Message));
      return;
   end if;

   -- Be sure the key is available.
   Cryptographic_Services.Initialize_Key(Crypto_Status);
   if Crypto_Status /= Cryptographic_Services.Success then
      Ada.Text_IO.Put_Line("*** Unable to intialize the cryptographic key");
      return;
   end if;

   -- Initialize the data storage. This procedure raises an exception if it fails.
   -- TODO: Handle the exception raised (or maybe change the procedure to return a status code).
   Data_Storage.Initialize;

   -- Initialize the remote access. This procedure raises an exception if it fails.
   -- TODO: Handle the exception raised (or maybe change the procedure to return a status code).
   --Remote_Access.Initialize;

   -- Set up the socket. This initializes the network streams (both input and output).
   Network.Socket.Create_And_Bind_Socket(Network.Addresses.Port_Type'Value(Get_Switch(Port)));

   -- Service_Clients never returns.
   -- TODO: Come up with a good way to cleanly shut the server down.
   Server_SPARK_Boundary.Service_Clients;

exception
   when Ex : Network.Socket.Network_Error =>
      Ada.Text_IO.Put_Line("*** Unable to initialize network: " & Exception_Message(Ex));
      --Remote_Access.Shutdown;
      Data_Storage.Shutdown;

end Thumper_Server;
