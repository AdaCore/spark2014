---------------------------------------------------------------------------
-- FILE    : timestamp_messages-client.adb
-- SUBJECT : Body of a package for encoding/decoding timestamps on the client side.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package body Timestamp_Messages.Client is

   procedure Get_Timestamp_Value
     (Message : in  Hermes.Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Stamp   : out Timestamp;
      Status  : out Hermes.DER.Status_Type) is
   begin
      raise Program_Error with "Timestamp_Messages.Get_Timestamp_Value not implemented";
   end Get_Timestamp_Value;


   function Put_Request_Value(Req : Request) return Hermes.Octet_Array is
      Dummy : Hermes.Octet_Array(1 .. 0);
   begin
      raise Program_Error with "Timestamp_Messages.Client.Put_Request_Value not implemented";
      return Dummy;
   end Put_Request_Value;


   procedure Get_Response_Value
     (Message : in  Hermes.Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Resp    : out Response;
      Status  : out Hermes.DER.Status_Type) is
   begin
      raise Program_Error with "Timestamp_Messages.Client.Get_Response_Value not implemented";
   end Get_Response_Value;


end Timestamp_Messages.Client;
