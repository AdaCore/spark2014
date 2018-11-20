---------------------------------------------------------------------------
-- FILE    : timestamp_messages-server.adb
-- SUBJECT : Body of a package for encoding/decoding timestamps on the server side.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Hermes.DER.Encode;

use Hermes;
use Hermes.DER;
use Hermes.DER.Encode;

package body Timestamp_Messages.Server is

   function Put_Timestamp_Value(Stamp : Timestamp) return Hermes.Octet_Array is
      Message_Imprint : constant Hermes.Octet_Array :=
        Put_OID_Value(Stamp.Hash_Algorithm) & Put_Octet_String_Value(Stamp.Hashed_Message);

      Message_Imprint_Value : constant Hermes.Octet_Array :=
        (Make_Leading_Identifier
           (Tag_Class       => Class_Universal,
            Structured_Flag => Constructed,
            Tag             => Tag_Sequence) & Put_Length_Value(Message_Imprint'Length) &
                                                                               Message_Imprint);

      TST_Info : constant Hermes.Octet_Array :=
        Put_Integer_Value(Stamp.Version) &
        Put_OID_Value(Stamp.Policy)      &
        Message_Imprint_Value            &
        Put_Integer_Value(Integer(Stamp.Serial_Number)); -- TODO: Will cause Constraint_Error!
        -- TODO: Add the all important generalized time field!
   begin
      return
        (Make_Leading_Identifier
           (Tag_Class       => Class_Universal,
            Structured_Flag => Constructed,
            Tag             => Tag_Sequence) & Put_Length_Value(TST_Info'Length) & TST_Info);
   end Put_Timestamp_Value;


   procedure Get_Request_Value
     (Message : in  Hermes.Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Req     : out Request;
      Status  : out Hermes.DER.Status_Type) with SPARK_Mode => Off is
   begin
      raise Program_Error with "Timestamp_Messages.Server.Get_Request_Value not implemented";
   end Get_Request_Value;


   function Put_Response_Value(Resp : Response) return Hermes.Octet_Array with SPARK_Mode => Off is
      Dummy : Hermes.Octet_Array(1 .. 0);
   begin
      raise Program_Error with "Timestamp_Messages.Server.Put_Response_Value not implemented";
      return Dummy;
   end Put_Response_Value;


end Timestamp_Messages.Server;
