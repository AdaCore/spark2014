---------------------------------------------------------------------------
-- FILE    : server_spark_boundar.adb
-- SUBJECT : Body of a package enclosing the SPARK portion of the server.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Messages;
with Network.Addresses;
with Server_Timestamp_Maker;

package body Server_SPARK_Boundary is

   procedure Service_Clients is
      use type Reader.Status_Type;
      use type Writer.Status_Type;

      Client_Address   : Network.Addresses.UDPv4;

      Network_Request  : Messages.Network_Message;  -- Low level request.
      Request_Message  : Messages.Message;          -- Converted to Hermes.Octets.
      Read_Status      : Reader.Status_Type;

      Response_Message : Messages.Message;          -- High level request.
      Network_Response : Messages.Network_Message;  -- Converted to Network.Octets.
      Write_Status     : Writer.Status_Type;
   begin
      -- Service clients infinitely.
      -- TODO: Come up with a way to cleanly shut the server down.
      loop
         Reader.Receive(Message => Network_Request, From => Client_Address, Status => Read_Status);
         if Read_Status /= Reader.Success then
            Logger.Write_Error("Failure reading request message!");
         else
            Request_Message := Messages.From_Network(Network_Request);
            Server_Timestamp_Maker.Create_Timestamp(Request_Message, Response_Message);
            Network_Response := Messages.To_Network(Response_Message);

            Writer.Send(Message => Network_Response, To => Client_Address, Status => Write_Status);
            if Write_Status /= Writer.Success then
               Logger.Write_Error("Failure sending reply message!");
            end if;
         end if;
      end loop;
   end Service_Clients;

end Server_SPARK_Boundary;
