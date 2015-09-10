---------------------------------------------------------------------------
-- FILE    : server_timestamp_maker.adb
-- SUBJECT : Body of a package that encapsulates the work of creating a time stamp.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Hermes;
with Hermes.DER;
with Hermes.DER.Decode;

package body Server_Timestamp_Maker is
   use type Hermes.Octet;
   use type Hermes.DER.Status_Type;

   type Status_Type is (Success, Failure);

   type Imprint is
      record
         X : Integer; -- TODO: Replace with appropriate content.
      end record;

   -- Extracts message imprint from request. The meaning of the parameters are as follows.
   --   Request_Message : The request message from the client.
   --   Index           : The first position in Request_Message where the imprint starts.
   --   Stop            : The last position of the imprint.
   --   Message_Imprint : The imprint obtained from the message.
   --   Message_Status  : Indicates the success or failure of imprint extraction.
   --
   procedure Get_Message_Imprint
     (Request_Message : in  Messages.Message;
      Index           : in  Messages.Index_Type;
      Stop            : out Messages.Index_Type;
      Message_Imprint : out Imprint;
      Imprint_Status  : out Status_Type) is
   begin
      null;
   end Get_Message_Imprint;


   function Valid_Request(Request_Message : in Messages.Message) return Boolean is

      Result          : Boolean := True;
      Length_Stop     : Messages.Index_Type;
      Length          : Natural;
      Version_Stop    : Messages.Index_Type;
      Version         : Integer;
      Imprint_Stop    : Messages.Index_Type;
      Message_Imprint : Imprint;
      Decode_Status   : Hermes.DER.Status_Type;
      Imprint_Status  : Status_Type;
   begin
      -- TODO: All these complex nested conditionals are nasty.
      -- Come up with a better way to handle this.

      if Request_Message.Size <= 2 then
         -- The message is too short. It can't possibly make sense. This check ensures certain
         -- array accesses below will work.
         Result := False;
      elsif Request_Message.Data(Request_Message.Data'First) /= 16#30# then
         -- The message is not a sequence.
         Result := False;
      else
         -- Get the length of the sequence.
         Hermes.DER.Decode.Get_Length_Value
           (Request_Message.Data, Request_Message.Data'First + 1, Length_Stop, Length, Decode_Status);
         if Decode_Status /= Hermes.DER.Success then
            -- Can't decode the sequence length.
            Result := False;
         elsif Length_Stop + Length /= Request_Message.Data'Last then
            -- Message has the wrong length.
            Result := False;
         else
            -- Get the version number.
            Hermes.DER.Decode.Get_Integer_Value
              (Request_Message.Data, Length_Stop + 1, Version_Stop, Version, Decode_Status);
            if Decode_Status /= Hermes.DER.Success then
               -- Can't decode the version.
               Result := False;
            elsif Version /= 1 then
               -- Bad version.
               Result := False;
            else
               -- Get the message imprint.
               Get_Message_Imprint
                 (Request_Message => Request_Message,
                  Index           => Version_Stop + 1,
                  Stop            => Imprint_Stop,
                  Message_Imprint => Message_Imprint,
                  Imprint_Status  => Imprint_Status);

               if Imprint_Status /= Success then
                  -- Can't decode the imprint.
                  Result := False;
               else
                  raise Program_Error
                    with "Incomplete implementation (Timestamp_Maker.Valid_Request)";
               end if;
            end if;
         end if;
      end if;
      return Result;
   end Valid_Request;


   procedure Create_Timestamp
     (Request_Message  : in  Messages.Message; Response_Message : out Messages.Message) is
   begin
      Response_Message := Messages.Message'(Data => (others => 0), Size => 0);

      if not Valid_Request(Request_Message) then
         raise Program_Error
           with "Incomplete implementation (Timestamp_Maker.Create_Timestamp; bad request)";
      else
         raise Program_Error
           with "Incomplete implementation (Timestamp_Maker.Create_Timestamp; good request)";
      end if;
   end Create_Timestamp;


end Server_Timestamp_Maker;
