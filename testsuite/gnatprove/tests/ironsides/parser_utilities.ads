----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

with DNS_Types,
     RR_Type,
     RR_Type.AAAA_Record_Type,
     RR_Type.DNSKey_Record_Type,
     RR_Type.RRSig_Record_Type,
     Unsigned_Types;

use type Unsigned_Types.Unsigned16,
         Unsigned_Types.Unsigned32,
         RR_Type.RRItemType;

--with Ada.Text_IO, Ada.Integer_Text_IO;

package Parser_Utilities is

   procedure CheckAndAppendOrigin
     (Target      : in out RR_Type.DomainNameStringType;
      Origin      : in     RR_Type.DomainNameStringType;
      CurrentLine : in     RR_Type.LineFromFileType;
      LastPos     : in     RR_Type.Linelengthindex;
      LineCount   : in     Unsigned_Types.Unsigned32;
      Success     : in out Boolean)
   with Depends => ((Success, Target) => (Origin, Success, Target),
                    null => (CurrentLine, LastPos, LineCount));

   procedure CheckValidHostName
     (Name    : in     RR_Type.DomainNameStringType;
      Success : in out Boolean)
   with Depends => (Success =>+ Name);

   procedure CheckValidSrvOwner
     (Name    : in     RR_Type.DomainNameStringType;
      Success : in out Boolean)
   with Depends => (Success =>+ Name);


   procedure FindFirstToken
     (S      : in     RR_Type.LineFromFileType;
      Length : in     RR_Type.LineLengthIndex;
      T      :    out RR_Type.RRItemType)
   with Depends => (T => (Length, S));

   procedure FindNextToken
     (S      : in     RR_Type.LineFromFileType;
      Length : in     RR_Type.LineLengthIndex;
      BegIdx : in out RR_Type.LineLengthIndex;
      EndIdx :    out RR_Type.LineLengthIndex;
      T      :    out RR_Type.RRItemType)
   with Depends => ((BegIdx, EndIdx, T) => (BegIdx, Length, S)),
        Pre     => BegIdx <= Length,
        Post    => BegIdx <= EndIdx and
                   BegIdx <= Length and
                   EndIdx <= Length and
                   (if T = RR_Type.Number then
                      (for all I in Integer range BegIdx .. EndIdx =>
                         S (I) >= '0' and S (I) <= '9'));

   procedure Convert8BitUnsigned
     (Value        :    out Unsigned_Types.Unsigned8;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      BegIdx       : in     RR_Type.LineLengthIndex;
      EndIdx       : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => (Success =>+ (BegIdx, EndIdx, ZoneFileLine),
                    Value => (BegIdx, EndIdx, ZoneFileLine)),
        Pre     => (for all I in integer range BegIdx .. EndIdx =>
                      ZoneFileLine (I) >= '0' and ZoneFileLine (I) <= '9');

   procedure Convert16BitUnsigned
     (Value        :    out Unsigned_Types.Unsigned16;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      BegIdx       : in     RR_Type.LineLengthIndex;
      EndIdx       : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => (Success =>+ (BegIdx, EndIdx, ZoneFileLine),
                    Value => (BegIdx, EndIdx, ZoneFileLine)),
        Pre     => (for all I in Integer range BegIdx .. EndIdx =>
                      ZoneFileLine (I) >= '0' and ZoneFileLine(I) <= '9');

   procedure Convert32BitUnsigned
     (Value        :    out Unsigned_Types.Unsigned32;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      BegIdx       : in     RR_Type.LineLengthIndex;
      EndIdx       : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => (Success =>+ (BegIdx, EndIdx, ZoneFileLine),
                    Value => (BegIdx, EndIdx, ZoneFileLine)),
        Pre     => (for all I in Integer range BegIdx .. EndIdx =>
                      ZoneFileLine (I) >= '0' and ZoneFileLine (I) <= '9');

   procedure ConvertTimeSpec
     (S      : in     RR_Type.LineFromFileType;
      BegIdx : in     RR_Type.LineLengthIndex;
      EndIdx : in     RR_Type.LineLengthIndex;
      RetVal :    out Unsigned_Types.Unsigned32;
      Success: in out Boolean)
   with Depends => ((RetVal, Success) => (BegIdx, EndIdx, S, Success));

   procedure ConvertTimeString
     (TimeVal    :    out Unsigned_Types.Unsigned32;
      TimeString : in     RR_Type.RRSig_Record_Type.TimeStringType;
      Success    : in out Boolean)
   with Depends => (Success =>+ TimeString,
                    TimeVal => TimeString),
        Pre     => (for all I in
                      RR_Type.RRSig_Record_Type.TimeStringTypeIndex =>
                      TimeString (I) >= '0' and TimeString (I) <= '9');

   procedure AddToKeyR
     (RRSig_Rec : in out RR_Type.RRSig_Record_Type.RRSigRecordType;
      S         : in     RR_Type.LineFromFileType;
      Length    : in     RR_Type.LineLengthIndex;
      AllDone   :    out Boolean;
      Success   : in out Boolean)
   with Depends => (AllDone => (Length, S),
                    (RRSig_Rec, Success) =>+ (Length, RRSig_Rec, S));

   procedure AddToKey
     (DNSKey_Rec : in out RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
      S          : in     RR_Type.LineFromFileType;
      Length     : in     RR_Type.LineLengthIndex;
      Success    : in out Boolean)
   with Depends => ((DNSKey_Rec, Success) =>+ (DNSKey_Rec, Length, S));

   function ConvertIPV4
     (S      : in RR_Type.LineFromFileType;
      BegIdx : in RR_Type.LineLengthIndex;
      EndIdx : in RR_Type.LineLengthIndex)
      return Unsigned_Types.Unsigned32;

   function ConvertIPV6
     (S      : in RR_Type.LineFromFileType;
      BegIdx : in RR_Type.LineLengthIndex;
      EndIdx : in RR_Type.LineLengthIndex)
      return RR_Type.AAAA_Record_Type.IPV6AddrType;

   function GetRecordType
     (S      : in RR_Type.LineFromFileType;
      BegIdx : in RR_Type.LineLengthIndex;
      EndIdx : in RR_Type.LineLengthIndex)
      return DNS_Types.Query_Type
   with Pre => BegIdx <= EndIdx;

end Parser_Utilities;
