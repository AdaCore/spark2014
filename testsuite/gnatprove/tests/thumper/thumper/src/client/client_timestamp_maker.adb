---------------------------------------------------------------------------
-- FILE    : client_timestamp_maker.adb
-- SUBJECT : Body of a package that encapsulates the work of creating a timestamp.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

-- TODO: It might be better to define a boundary variable package for console I/O.
with Ada.Text_IO;
with Messages;
with Network.Addresses;
with Network.Socket;
with Network.Socket.Writer;

use Messages;
use Network;
use Network.Socket;

package body Client_Timestamp_Maker is

   procedure Create_Timestamp
     (Hash           : in  Hermes.Octet_Array;
      Timestamp      : out Hermes.Octet_Array;
      Timestamp_Size : out Natural) is

      use type Addresses.Status_Type;
      use type Writer.Status_Type;

      -- TODO: Need to get host name and port from the command line outside the SPARK boundary.
      procedure Make_Request is
         Local_Host      : Addresses.IPv4;
         Request_Message : Network_Message;
         Network_Status  : Writer.Status_Type;
         Address_Status  : Addresses.Status_Type;
      begin
         Request_Message := (Data => (others => 0), Size => 0);
         Addresses.To_IPv4_Address("127.0.0.1", Local_Host, Address_Status);
         if Address_Status /= Addresses.Success then
            Ada.Text_IO.Put_Line("Failed to convert target address to binary form!");
         else
            -- TODO: Use the encoded request message here instead of this silly placeholder.
            Request_Message.Data(Messages.Index_Type'First) := Character'Pos('X');
            Writer.Send
              (Request_Message, Addresses.To_UDPv4_Address(Local_Host, 4318), Network_Status);
            if Network_Status /= Writer.Success then
               Ada.Text_IO.Put_Line("Failed to send request message!");
            end if;
         end if;
      end Make_Request;

   begin
      -- Encode a request message.
      -- Send request to server.
      -- Receive response from server.
      -- Decode response and verify correctness.
      raise Program_Error with "Timestamp_Maker.Create_Timestamp not implemented";
   end Create_Timestamp;


   function Verify_Timestamp
     (Hash : Hermes.Octet_Array; Timestamp : Hermes.Octet_Array) return Boolean is
   begin
      -- Decode time stamp and verify correctness.
      raise Program_Error with "Timestamp_Maker.Verify_Timestamp not implemented";
      return False;
   end Verify_Timestamp;


end Client_Timestamp_Maker;
