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
     RR_Type.NSec_Record_Type,
     RR_Type.RRSig_Record_Type,
     Unsigned_Types;
--with Ada.Text_IO, Ada.Integer_Text_IO;


package Zone_File_Parser is
   type Unsigned8 is mod 2**8;

   procedure ParseDNSKeyHeader
     (DNSKey_Rec   :    out RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => ((DNSKey_Rec, Success) => (Success, ZLength, ZoneFileLine));

   procedure ParseRRSigHeader
     (RRSig_Rec    :    out RR_Type.RRSig_Record_Type.RRSigRecordType;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => ((RRSig_Rec, Success) => (Success, ZLength, ZoneFileLine));

   procedure ParseRRSig2ndLine
     (RRSig_Rec    : in out RR_Type.RRSig_Record_Type.RRSigRecordType;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => ((RRSig_Rec, Success) =>+ (Success, ZLength, ZoneFileLine));

   procedure ParseControlLine
     (NewOrigin    : in out RR_Type.DomainNameStringType;
      NewTTL       : in out Unsigned_Types.Unsigned32;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => ((NewOrigin, Success) =>+ (ZLength, ZoneFileLine),
                    NewTTL =>+ (Success, ZLength, ZoneFileLine));

   procedure ParseDomainName
     (NewDomainName :    out RR_Type.DomainNameStringType;
      ZoneFileLine  : in     RR_Type.LineFromFileType;
      ZLength       : in     RR_Type.LineLengthIndex;
      Success       : in out Boolean)
   with Depends => (NewDomainName => (ZLength, ZoneFileLine),
                    Success =>+ (ZLength, ZoneFileLine));

   procedure ParseDomainNameAndRRString
     (NewDomainName :    out RR_Type.DomainNameStringType;
      RRString      :    out RR_Type.LineFromFileType;
      ZoneFileLine  : in     RR_Type.LineFromFileType;
      ZLength       : in     RR_Type.LineLengthIndex;
      Success       : in out Boolean)
   with Depends => ((NewDomainName, RRString) => (ZLength, ZoneFileLine),
                    Success =>+ (ZLength, ZoneFileLine));

   procedure FillBlockInfo
     (RRString            : in     RR_Type.LineFromFileType;
      NumberOfRecordTypes :    out RR_Type.NSec_Record_Type.RecordTypeIndexValue;
      RecordTypes         :    out RR_Type.NSec_Record_Type.RecordTypeArrayType;
      NumberOfBlocks      :    out RR_Type.NSec_Record_Type.BlockNumberValue;
      BlockNumbers        :    out RR_Type.NSec_Record_Type.BlockNumberArrayType;
      BlockLengths        :    out RR_Type.NSec_Record_Type.BlockLengthArrayType;
      BitMaps             :    out RR_Type.NSec_Record_Type.BitMapsArrayArrayType;
      LineCount           : in     Unsigned_Types.Unsigned32;
      Success             : in out Boolean)
   with Depends => ((BitMaps,
                     BlockLengths,
                     BlockNumbers,
                     NumberOfBlocks,
                     NumberOfRecordTypes,
                     RecordTypes) => RRString,
                    Success =>+ RRString,
                    null => LineCount),
        Post    => (if Success then NumberOfBlocks > 0);

   procedure ParseIPV4
     (NewIPV4      :    out Unsigned_Types.Unsigned32;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => (NewIPV4 => (ZLength, ZoneFileLine),
                    Success =>+ (ZLength, ZoneFileLine));

   procedure ParseIPV6
     (NewIPV6      :    out RR_Type.AAAA_Record_Type.IPV6AddrType;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => (NewIPV6 => (ZLength, ZoneFileLine),
                    Success =>+ (ZLength, ZoneFileLine));

   procedure ParsePrefAndDomainName
     (NewPref       :    out Unsigned_Types.Unsigned16;
      NewDomainName :    out RR_Type.DomainNameStringType;
      ZoneFileLine  : in     RR_Type.LineFromFileType;
      ZLength       : in     RR_Type.LineLengthIndex;
      Success       : in out Boolean)
   with Depends => ((NewDomainName, NewPref) => (ZLength, ZoneFileLine),
                    Success =>+ (ZLength, ZoneFileLine));

   procedure ParsePrefWeightPortAndDomainName
     (NewPref       :    out Unsigned_Types.Unsigned16;
      NewWeight     :    out Unsigned_Types.Unsigned16;
      NewPort       :    out Unsigned_Types.Unsigned16;
      NewDomainName :    out RR_Type.DomainNameStringType;
      ZoneFileLine  : in     RR_Type.LineFromFileType;
      ZLength       : in     RR_Type.LineLengthIndex;
      Success       : in out Boolean)
   with Depends => ((NewDomainName,
                     NewPort,
                     NewPref,
                     NewWeight) => (ZLength, ZoneFileLine),
                    Success =>+ (ZLength, ZoneFileLine));

   procedure ParseNameServerAndEmail
     (NewNameServer :    out RR_Type.DomainNameStringType;
      NewEmail      :    out RR_Type.DomainNameStringType;
      ZoneFileLine  : in     RR_Type.LineFromFileType;
      ZLength       : in     RR_Type.LineLengthIndex;
      Success       : in out Boolean)
   with Depends => ((NewEMail, NewNameServer) => (ZLength, ZoneFileLine),
                    Success =>+ (ZLength, ZoneFileLine));

   procedure ParseSerialNumber
     (NewSerialNumber :    out Unsigned_Types.Unsigned32;
      ZoneFileLine    : in     RR_Type.LineFromFileType;
      ZLength         : in     RR_Type.LineLengthIndex;
      Success         : in out Boolean)
   with Depends => (NewSerialNumber => (ZLength, ZoneFileLine),
                    Success =>+ (ZLength, ZoneFileLine));

   procedure ParseTimeSpec
     (NewTimeSpec  :    out Unsigned_Types.Unsigned32;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => ((NewTimeSpec, Success) => (Success, ZLength, ZoneFileLine));

   procedure ParseOwnerTTLClassAndRecordType
     (NewOwner     : in out RR_Type.DomainNameStringType;
      NewTTL       : in out Unsigned_Types.Unsigned32;
      NewClass     : in out RR_Type.ClassType;
      NewType      : in out DNS_Types.Query_Type;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   with Depends => ((NewClass,
                     NewTTL,
                     NewType,
                     Success) =>+ (Success, ZLength, ZoneFileLine),
                    NewOwner =>+ (ZLength, ZoneFileLine));

end Zone_File_Parser;
