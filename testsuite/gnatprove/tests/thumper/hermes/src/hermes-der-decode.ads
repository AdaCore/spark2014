---------------------------------------------------------------------------
-- FILE    : hermes-der-decode.ads
-- SUBJECT : Specification of a package for decoding DER encoded data.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package Hermes.DER.Decode is

   -- Splits a leading identifier octet into its constituent parts. Fails with
   -- DER.Bad_Identifier if Value is an invalid first identifier octet.
   --
   procedure Split_Leading_Identifier
     (Value           : in  Octet;
      Tag_Class       : out Tag_Class_Type;
      Structured_Flag : out Structured_Flag_Type;
      Tag             : out Leading_Number_Type;
      Status          : out Status_Type)
     with
       Depends => ( (Tag_Class, Structured_Flag, Tag, Status) => Value);


   -- Examines the Message starting at position Start looking for a DER encoded length.
   --
   -- Message => The message to examine.
   -- Start   => The starting position in the message where the length is to be extracted.
   -- Stop    => The last position in the message used by the encoded length.
   -- Length  => The extracted length.
   -- Status  => The status of the extraction (success/failure, etc).
   --
   -- Decodes a DER encoded length from the given message. Fails with DER.Indefinite_Length if
   -- the encoded length is in the indefinite form. In that case the returned Length is zero
   -- and the returned Stop is at the last octet of the encoded length as usual. Fails with
   -- DER.Bad_Length if the length is not encoded properly. In that case the returned Length is
   -- zero and the returned Stop is undefined (it will depend on the precise nature of the
   -- encoding problem). Fails with DER.Unimplemented_Length if the encoded length is too large
   -- for this implementation to handle. In that case the returned Length is zero and the
   -- returned Stop is at the last octet of the encoded length as usual.
   --
   procedure Get_Length_Value
     (Message : in  Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Length  : out Natural;
      Status  : out Status_Type)
     with
       Depends => ( (Stop, Length, Status) => (Message, Start) ),
       Pre => Start in Message'Range,
       Post => Stop in Start .. Message'Last;


   -- Examines the Message starting at position Start looking for a DER encoded Boolean.
   --
   -- Message => The message to examine.
   -- Start   => The starting position in the message where the Boolean is to be extracted.
   -- Stop    => The last position in the message used by the encoded Boolean.
   -- Value   => The extracted Boolean.
   -- Status  => The status of the extraction (success/failure, etc).
   --
   -- Decodes a DER encoded Boolean from the given message. Fails with DER.Bad_Value if the data
   -- is not encoded properly. In that case the returned Value is False and the returned Stop is
   -- undefined (it will depend on the precise nature of the encoding problem).
   --
   procedure Get_Boolean_Value
     (Message : in  Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Value   : out Boolean;
      Status  : out Status_Type)
     with
       Depends => ( (Stop, value, Status) => (Message, Start) ),
       Pre => Start in Message'Range,
       Post => Stop in Start .. Message'Last;


   -- Examines the Message starting at position Start looking for a DER encoded integer.
   --
   -- Message => The message to examine.
   -- Start   => The starting position in the message where the integer is to be extracted.
   -- Stop    => The last position in the message used by the encoded integer.
   -- Value   => The extracted integer.
   -- Status  => The status of the extraction (success/failure, etc).
   --
   -- Decodes a DER encoded integer from the given message. Fails with DER.Bad_Value if the data
   -- is not encoded properly. In that case the returned Value is zero and the returned Stop is
   -- undefined (it will depend on the precise nature of the encoding problem). Fails with
   -- DER.Unimplemented_Value if the encoded value is too large for this implementation to
   -- handle. In that case the returned Value is zero and the returned Stop is at the last octet
   -- of the encoded value as usual.
   --
   procedure Get_Integer_Value
     (Message : in  Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Value   : out Integer;
      Status  : out Status_Type)
     with
       Depends => ( (Stop, value, Status) => (Message, Start) ),
       Pre => Start in Message'Range,
       Post => Stop in Start .. Message'Last;

end Hermes.DER.Decode;
