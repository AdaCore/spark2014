--------------------------------------------------------------------------------
-- FILE   : cubedos-lib-xdr.ads
-- SUBJECT: Specification of an XDR encoding/decoding package.
-- AUTHOR : (C) Copyright 2015 by Vermont Technical College
--
-- XDR is a standard for converting typed data into an octet stream suitable for exchange
-- between communicating partners. Unlike ASN.1, the data is not self describing so the
-- receiver needs to know what information to expect in what order. See RFC-4506 for more
-- information: http://tools.ietf.org/html/rfc4506.html.
--
--------------------------------------------------------------------------------
pragma SPARK_Mode(On);

package CubedOS.Lib.XDR is

   -------------------
   -- Type Definitions
   -------------------

   -- TODO: Should we remove the XDR prefix?
   -- The names would be nicer, but they might be confused with those in package Standard.
   type XDR_Integer is range -2**31 .. 2**31 - 1;
   type XDR_Unsigned is mod 2**32;
   type XDR_Boolean is (XDR_False, XDR_True);
   type XDR_Hyper is range -2**63 .. 2**63 - 1;
   type XDR_Unsigned_Hyper is mod 2**64;
   -- TODO: Add support for XDR floating point types? Maybe someday.

   -- This type is used for both "opaque data" and for encoded data.
   type Octet is mod 2**8;

   -- Limiting the maximum size of XDR related arrays simplfies proving freedom from overflow
   -- in array index computations. There is no other particular reason for this limit; it is
   -- arbitrary. The limit should be high enough to satisfy any reasonable application.
   --
   Maximum_Array_Size : constant := 2**16;

   -- Starting the index type at 0 is convenient when expressing "multiple of four" assertions.
   -- The 'extended' type provides an extra value before the first allowed index. This is used
   -- by the Octet_Array and String encoders so they can return a correct 'Last' when given zero
   -- length values to encode. Support for encoding zero length arrays and strings is useful.
   --
   subtype Octet_Array_Index is Natural range 0 .. Maximum_Array_Size - 1;
   subtype Octet_Array_Extended_Index is Integer range -1 .. Maximum_Array_Size - 1;
   subtype Octet_Array_Count is Natural range 0 .. Maximum_Array_Size;
   type Octet_Array is array(Octet_Array_Index range <>) of Octet;


   ----------------------
   -- Encoding Procedures
   ----------------------

   -- Encodes an XDR integer into Data starting at Position.
   procedure Encode
     (Value    : in     XDR_Integer;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Index)
     with
       Global  => null,
       Depends => (Data =>+ (Value, Position), Last => Position),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (4 - 1) <= Data'Last,
       Post => Last = Position + (4 - 1);

   -- Encodes an XDR unsigned integer into Data starting at Position.
   procedure Encode
     (Value    : in     XDR_Unsigned;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Index)
     with
       Global  => null,
       Depends => (Data =>+ (Value, Position), Last => Position),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (4 - 1) <= Data'Last,
       Post => Last = Position + (4 - 1);

   -- Encodes an XDR Boolean into Data starting at Position.
   procedure Encode
     (Value    : in     XDR_Boolean;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Index)
     with
       Global  => null,
       Depends => (Data =>+ (Value, Position), Last => Position),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (4 - 1) <= Data'Last,
       Post => Last = Position + (4 - 1);

   -- Encodes an XDR hyper integer into Data starting at Position.
   procedure Encode
     (Value    : in     XDR_Hyper;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Index)
     with
       Global  => null,
       Depends => (Data =>+ (Value, Position), Last => Position),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (8 - 1) <= Data'Last,
       Post => Last = Position + (8 - 1);

   -- Encodes an XDR unsigned hyper integer into Data starting at Position.
   procedure Encode
     (Value    : in     XDR_Unsigned_Hyper;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Index)
     with
       Global  => null,
       Depends => (Data =>+ (Value, Position), Last => Position),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (8 - 1) <= Data'Last,
     Post => Last = Position + (8 - 1);

   function Length_With_Padding(Length : Octet_Array_Count) return Octet_Array_Count is
     (Length + (if Length rem 4 = 0 then 0 else (4 - Length rem 4)));

   -- Encodes XDR fixed length opaque data into Data starting at Position.
   procedure Encode
     (Value    : in     Octet_Array;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Extended_Index)
     with
       Global  => null,
       Depends => (Data =>+ (Value, Position), Last => (Value, Position)),
       Pre =>
         Position rem 4 = 0 and then
         Data'Length > 0 and then
         Data'Length rem 4 = 0 and then
         Position in Data'Range and then
         Length_With_Padding(Value'Length) <= (Data'Last - Position) + 1,
       Post => Last = Position + (Length_With_Padding(Value'Length) - 1);

   -- Encodes XDR fixed length string into Data starting at Position.
   procedure Encode
     (Value    : in     String;
      Data     : in out Octet_Array;
      Position : in     Octet_Array_Index;
      Last     :    out Octet_Array_Extended_Index)
     with
       Global  => null,
       Depends => (Data =>+ (Value, Position), Last => (Value, Position)),
       Pre =>
         Position rem 4 = 0 and then
         Data'Length > 0 and then
         Data'Length rem 4 = 0 and then
         Value'Length <= Octet_Array_Count'Last and then
         Position in Data'Range and then
         Length_With_Padding(Value'Length) <= (Data'Last - Position) + 1,
       Post => Last = Position + (Length_With_Padding(Value'Length) - 1);


   ----------------------
   -- Decoding Procedures
   ----------------------

   -- Decodes an integer from Data starting at Position up to and including Last.
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out XDR_Integer;
      Last     : out Octet_Array_Index)
     with
       Global  => null,
       Depends => (Value => (Data, Position), Last => Position),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (4 - 1) <= Data'Last,
       Post => Last = Position + (4 - 1);

   -- Decodes an unsigned integer from Data starting at Position up to and including Last.
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out XDR_Unsigned;
      Last     : out Octet_Array_Index)
     with
       Global  => null,
       Depends => (Value => (Data, Position), Last => Position),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (4 - 1) <= Data'Last,
       Post => Last = Position + (4 - 1);

   -- Decodes a Boolean from Data starting at Position up to and including Last.
   -- TODO: What should be done if the information in Data is invalid?
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out XDR_Boolean;
      Last     : out Octet_Array_Index)
     with
       Global  => null,
       Depends => (Value => (Data, Position), Last => Position),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (4 - 1) <= Data'Last,
       Post => Last = Position + (4 - 1);

   -- Decodes a hyper integer from Data starting at Position up to and including Last.
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out XDR_Hyper;
      Last     : out Octet_Array_Index)
     with
       Global  => null,
       Depends => (Value => (Data, Position), Last => Position),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (8 - 1) <= Data'Last,
       Post => Last = Position + (8 - 1);

   -- Decodes an unsigned hyper integer from Data starting at Position up to and including Last.
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out XDR_Unsigned_Hyper;
      Last     : out Octet_Array_Index)
     with
       Global  => null,
       Depends => (Value => (Data, Position), Last => Position),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (8 - 1) <= Data'Last,
       Post => Last = Position + (8 - 1);

   -- Decodes a fixed length array of opaque data from Data starting at Position.
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out Octet_Array;
      Last     : out Octet_Array_Extended_Index)
     with
       Global  => null,
       Depends => (Value =>+ (Data, Position), Last => (Position, Value)),
       Pre =>
         Position rem 4 = 0 and
         Data'Length rem 4 = 0 and
         Position in Data'Range and
         Position + (Length_With_Padding(Value'Length) - 1) <= Data'Last,
       Post => Last = Position + (Length_With_Padding(Value'Length) - 1);

   -- Decodes a fixed length string from Data starting at Position.
   procedure Decode
     (Data     : in  Octet_Array;
      Position : in  Octet_Array_Index;
      Value    : out String;
      Last     : out Octet_Array_Extended_Index)
     with
       Global  => null,
       Depends => (Value =>+ (Data, Position), Last => (Position, Value)),
       Pre =>
         Position rem 4 = 0 and then
         Data'Length > 0 and then
         Data'Length rem 4 = 0 and then
         Value'Length <= Octet_Array_Count'Last and then
         Position in Data'Range and then
         Position <= Data'Last - (Length_With_Padding(Value'Length) - 1),
       Post => Last = Position + (Length_With_Padding(Value'Length) - 1);

end CubedOS.Lib.XDR;
