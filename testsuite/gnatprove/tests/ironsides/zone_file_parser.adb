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

with Ada.Characters.Handling,
     Ada.Unchecked_Conversion,
     Error_Msgs, Parser_Utilities,
     RR_Type.Aaaa_Record_Type,
     RR_Type.NS_Record_Type,
     RR_Type.MX_Record_Type,
     RR_Type.Srv_Record_Type,
     RR_Type.SOA_Record_Type,
     DNS_Types,
     Unsigned_Types,
     Ada.Characters.Latin_1;
--with Ada.Text_IO, ada.Integer_Text_IO;

use type RR_Type.RRItemType,
         RR_Type.AAAA_Record_Type.IPV6AddrType,
         DNS_Types.Byte,
         DNS_Types.Query_Type,
         Unsigned_Types.Unsigned32,
         Unsigned_Types.Unsigned16,
         Unsigned_types.Unsigned8;

package body Zone_File_Parser is

   procedure ParseDNSKeyHeader
     (DNSKEY_Rec   :    out RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      Correct_Protocol_Value : constant Unsigned_Types.Unsigned8 := 3;
      BegIdx                 : RR_Type.LineLengthIndex := 1;
      EndIdx                 : RR_Type.LineLengthIndex;
      FoundType              : RR_Type.RRItemType;
   begin
      --SPARK requires all fields of OUT parameter records be assigned
      DNSKey_Rec := RR_Type.DNSKey_Record_Type.BlankDNSKeyRecord;

      --find the record type indicator, which must be present since this
      --routine was called
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);

      --second condition always true if precondition of routine is met, but it
      --helps the prover
      while FoundType /= RR_Type.RecordIndicator and EndIdx < ZLength loop
         BegIdx := ((BegIdx - BegIdx) + EndIdx) + 1;  --makes flow error go away
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
      end loop;

      --parse FLAG field (unsigned 16-bit #)
      if EndIdx = ZLength then
         Success := False;
      else
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         if FoundType /= RR_Type.Number then
            Success := False;
         else --convert token to 16-bit number
            Parser_Utilities.Convert16BitUnsigned (DNSKey_Rec.Flags,
                                                   ZoneFileLine,
                                                   BegIdx,
                                                   EndIdx,
                                                   Success);
         end if;
      end if;

      --parse PROTOCOL field (unsigned 8-bit #, must be 3)
      if Success then
         if EndIdx = ZLength then
            Success := False;
         else
            BegIdx := EndIdx + 1;
            Parser_Utilities.FindNextToken (ZoneFileLine,
                                            ZLength,
                                            BegIdx,
                                            EndIdx,
                                            FoundType);
            if FoundType /= RR_Type.Number then
               Success := False;
            else --convert token to unsigned 8-bit number
               Parser_Utilities.Convert8BitUnsigned (DNSKey_Rec.Protocol,
                                                     ZoneFileLine,
                                                     BegIdx,
                                                     EndIdx,
                                                     Success);
            end if;
            if DNSKey_Rec.Protocol /= Correct_Protocol_Value then
               Success := False;
            end if;
         end if;
      end if;

      --parse ALGORITHM field (unsigned 8-bit #)
      if Success then
         if EndIdx = ZLength then
            Success := False;
         else
            BegIdx := EndIdx + 1;
            Parser_Utilities.FindNextToken (ZoneFileLine,
                                            ZLength,
                                            BegIdx,
                                            EndIdx,
                                            FoundType);
            if FoundType /= RR_Type.Number then
               Success := False;
            else --convert token to unsigned 8-bit number
               Parser_Utilities.Convert8BitUnsigned (DNSKey_Rec.Algorithm,
                                                     ZoneFileLine,
                                                     BegIdx,
                                                     EndIdx,
                                                     Success);
            end if;
         end if;
      end if;
   end ParseDNSKeyHeader;

   --this is only called from ParseRRSigHeader, created because otherwise
   --ParseRRSigHeader is too complex for Examiner
   procedure ParseTypeCoveredAlgorithmNumLabels
     (RRSig_Rec    : in out RR_Type.RRSig_Record_Type.RRSigRecordType;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      EndIdx       : in out RR_Type.LineLengthIndex;
      Success      : in out Boolean)
     with Depends => ((EndIdx,
                       RRSig_Rec,
                       Success) =>+ (EndIdx, Success, ZLength, ZoneFileLine))
  is
      BegIdx    : RR_Type.LineLengthIndex;
      FoundType : Rr_Type.RrItemType;
   begin

      --TYPE_COVERED
      Success := Success and (EndIdx < ZLength);   --fail if at EOL
      if Success then
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         Success := FoundType = Rr_Type.RecordIndicator;
         if Success then
            RRSig_Rec.TypeCovered := Parser_Utilities.GetRecordType
                                       (ZoneFileLine, BegIdx, EndIdx);
         end if;
      end if;

      --ALGORITHM
      Success := Success and EndIdx < ZLength;   --fail if at EOL
      if Success then
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         Success := FoundType = RR_Type.Number;
         if Success then
            Parser_Utilities.Convert8BitUnsigned (RRSig_Rec.Algorithm,
                                                  ZoneFileLine,
                                                  BegIdx,
                                                  EndIdx,
                                                  Success);
         end if;
      end if;

      --NUM_LABELS
      Success := Success and EndIdx < ZLength;   --fail if at EOL
      if Success then
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         Success := FoundType = RR_Type.Number;
         if Success then
            Parser_Utilities.Convert8BitUnsigned (RRSig_Rec.NumLabels,
                                                  ZoneFileLine,
                                                  BegIdx,
                                                  EndIdx,
                                                  Success);
         end if;
      end if;

   end ParseTypeCoveredAlgorithmNumLabels;

   procedure ParseRRSigHeader
     (RRSig_Rec    :    out RR_Type.RRSig_Record_Type.RRSigRecordType;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      BegIdx     : RR_Type.LineLengthIndex := 1;
      EndIdx     : RR_Type.LineLengthIndex;
      FoundType  : RR_Type.RRItemType;

      TimeString : RR_Type.RRSig_Record_Type.TimeStringType :=
        RR_Type.RRSig_Record_Type.TimeStringType'(others => ' ');

   begin
      RRSig_Rec := RR_Type.RRSig_Record_Type.BlankRRSigRecord;

      --find the record type indicator (RRSIG), which must be present since
      --this routine was called
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);

      --second condition always true if precondition of routine is met, but it
      --helps the prover
      while FoundType /= RR_Type.RecordIndicator and EndIdx < ZLength loop
         BegIdx := EndIdx + 1;  --makes flow error go away
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
      end loop;

      --parse Type_Covered, Algorithm and Num_Labels fields
      ParseTypeCoveredAlgorithmNumLabels (RRSig_Rec,
                                          ZoneFileLine,
                                          ZLength,
                                          EndIdx,
                                          Success);

      --parse ORIG_TTL field (time spec)
      Success := Success and EndIdx < ZLength;   --fail if at EOL
      if Success then
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         if FoundType = RR_Type.Number then
            Parser_Utilities.Convert32BitUnsigned (RRSig_Rec.OrigTTL,
                                                   ZoneFileLine,
                                                   BegIdx,
                                                   EndIdx,
                                                   Success);
         elsif FoundType = RR_Type.DomainNameOrTimeSpec then
            Parser_Utilities.ConvertTimeSpec (ZoneFileLine,
                                              BegIdx,
                                              EndIdx,
                                              RRSig_Rec.OrigTTL,
                                              Success);
         else
            Success := False;
         end if;
      end if;

      --parse Sig_Expiration field (YYYYMMDDHHmmSS or unsigned 32-bit #)
      Success := Success and EndIdx < ZLength;   --fail if at EOL
      if Success then
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         Success := FoundType = RR_Type.Number;   --fail if not a number
      end if;

      if Success then   --next token is a number
         --convert token to unsigned 32-bit number
         --If it's not of length timeStringLength, can't be YYYYMMDDHHmmSS
         if EndIdx - BegIdx + 1 /=
           RR_Type.RRSig_Record_Type.TimeStringLength
         then
            Parser_Utilities.Convert32BitUnsigned (RRSig_Rec.OrigTTL,
                                                   ZoneFileLine,
                                                   BegIdx,
                                                   EndIdx,
                                                   Success);
         else --convert YYYYMMDDHHmmSS to #secs since 1 Jan 1970 00:00:00 UTC
            for I in RR_Type.RRSig_Record_Type.TimeStringTypeIndex loop
               pragma Loop_Invariant
                 (BegIdx = BegIdx'Loop_Entry and
                  EndIdx = EndIdx'Loop_Entry and
                  ZLength = Zlength'Loop_Entry and
                  EndIdx <= ZLength and
                  EndIdx - BegIdx =
                    RR_Type.RRSig_Record_Type.TimeStringLength - 1 and
                  I <= RR_Type.RRSig_Record_Type.TimeStringTypeIndex'Last);
               TimeString (I) := ZoneFileLine (BegIdx + I - 1);
            end loop;
            --establish and prove the precondition for ConvertTimeString (all
            --numbers)
            for I in RR_Type.RRSig_Record_Type.TimeStringTypeIndex loop
               pragma Loop_Invariant
                 (for all J in Integer range 1 .. I - 1 =>
                    TimeString (J) >= '0' and TimeString (J) <= '9');
               if TimeString (I) < '0' or TimeString (I) > '9' then
                  Success := False;
                  exit;
               end if;
            end loop;
            if Success then
               Parser_Utilities.ConvertTimeString (RRSig_Rec.SigExpiration,
                                                   TimeString,
                                                   Success);
            end if;
         end if; --timeString or simple number
      end if; --successful so far

      --parse left paren
      Success := Success and EndIdx < ZLength;   --fail if at EOL
      if Success then
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         --make bogus flow errors go away
         if FoundType /= RR_Type.LParen then
            Success := False;
         end if;
      end if;
   end ParseRRSigHeader;

   procedure ParseRRSig2ndLine
     (RRSig_Rec    : in out RR_Type.RRSig_Record_Type.RRSigRecordType;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      BegIdx        : RR_Type.LineLengthIndex;
      EndIdx        : RR_Type.LineLengthIndex;
      LengthOfToken : Rr_Type.LineLengthIndex;
      FoundType     : RR_Type.RRItemType;
      TimeString    : RR_Type.RRSig_Record_Type.TimeStringType :=
         RR_Type.RRSig_Record_Type.TimeStringType'(others => ' ');
   begin
      --parse Sig_Inception field (YYYYMMDDHHmmSS or unsigned 32-bit #)
      BegIdx := 1;
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);
      Success := Success and FoundType = RR_Type.Number;   --fail if not number

      if Success then   --next token is a number
         --convert token to unsigned 32-bit number
         --If it's not of length timeStringLength, can't be YYYYMMDDHHmmSS
         if EndIdx - BegIdx + 1 /=
              RR_Type.RRSig_Record_Type.TimeStringLength
         then
            Parser_Utilities.Convert32BitUnsigned (RRSig_Rec.OrigTTL,
                                                   ZoneFileLine,
                                                   BegIdx,
                                                   EndIdx,
                                                   Success);
         else --convert YYYYMMDDHHmmSS to #secs since 1 Jan 1970 00:00:00 UTC
            for I in RR_Type.RRSig_Record_Type.TimeStringTypeIndex loop
               pragma Loop_Invariant
                 (BegIdx = BegIdx'Loop_Entry and
                  EndIdx = EndIdx'Loop_Entry and
                  ZLength = ZLength'Loop_Entry and
                  EndIdx <= ZLength and
                  EndIdx - BegIdx =
                    RR_Type.RRSig_Record_Type.TimeStringLength - 1 and
                  I <= RR_Type.RRSig_Record_Type.TimeStringTypeIndex'Last);
               TimeString (I) := ZoneFileLine (BegIdx + I - 1);
            end loop;
            --establish and prove the precondition for ConvertTimeString (all
            --numbers)
            for I in RR_Type.RRSig_Record_Type.TimeStringTypeIndex loop
               pragma Loop_Invariant
                 (for all J in Integer range 1 .. I - 1 =>
                    TimeString (J) >= '0' and TimeString (J) <= '9');
               if TimeString (I) < '0' or TimeString (I) > '9' then
                  Success := False;
                  exit;
               end if;
            end loop;
            if Success then
               Parser_Utilities.ConvertTimeString (RRSig_Rec.SigInception,
                                                   TimeString,
                                                   Success);
            end if;
         end if; --TimeString or simple number
      end if; --successful so far

      --Key_Tag
      Success := Success and EndIdx < ZLength;   --fail if at EOL
      if Success then
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         Success := FoundType = RR_Type.Number;
         if Success then
            Parser_Utilities.Convert16BitUnsigned (RRSig_Rec.KeyTag,
                                                   ZoneFileLine,
                                                   BegIdx,
                                                   EndIdx,
                                                   Success);
         end if;
      end if;

      --Signer_Name
      Success := Success and EndIdx < ZLength;   --fail if at EOL
      if Success then
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         Success := FoundType = RR_Type.DomainNameOrTimeSpec;
         if Success then
            --SPARK caught these parens in the wrong place, nice!
            LengthofToken := (EndIdx - BegIdx) + 1;
            if LengthOfToken > RR_Type.MaxDomainNameLength then
               Success := False;
               Error_Msgs.PrintDomainLengthErrorInfo (ZoneFileLine,
                                                      BegIdx,
                                                      EndIdx);
            else
               --have a domain name, but must still pad it
               for I in Integer range BegIdx .. EndIdx loop
                  pragma Loop_Invariant
                    (BegIdx >= 1 and
                     EndIdx - BegIdx + 1 <= RR_Type.MaxDomainNameLength and
                     EndIdx = EndIdx'Loop_Entry);
                  RRSig_Rec.SignerName ((I + 1) - BegIdx) := ZoneFileLine (I);
               end loop;
               for I in Integer range EndIdx + 1.. RR_Type.MaxDomainNameLength
               loop
                  -- Remind prover that endIdx is in type
                  --# assert EndIdx >= 1;
                  pragma Loop_Invariant (EndIdx >= 1);
                  RRSIG_Rec.signerName(I) := ' ';
               end loop;
            end if;
         end if;
      end if;

      --to do
   end ParseRRSig2ndLine;


   --precondition is that zoneFileLine contains a record indicator, but can't
   --express that in SPARK
   procedure ParseDomainName
     (NewDomainName :    out RR_Type.DomainNameStringType;
      ZoneFileLine  : in     RR_Type.LineFromFileType;
      ZLength       : in     RR_Type.LineLengthIndex;
      Success       : in out Boolean)
   is
      BegIdx        : RR_Type.LineLengthIndex := 1;
      EndIdx        : RR_Type.LineLengthIndex;
      FoundType     : RR_Type.RRItemType;
      LengthOfToken : RR_Type.LineLengthIndex;

   begin
      NewDomainName := RR_Type.BlankDomainName;
      --find the record type indicator, which must be present since this
      --routine was called
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);

      --second condition always true if precondition of routine is met, but it
      --helps the prover
      while FoundType/= RR_Type.RecordIndicator and EndIdx < Zlength loop
         pragma Loop_Invariant (EndIdx < Zlength);
         BegIdx := EndIdx + 1;  --makes flow error go away
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
      end loop;

      --check to make sure something is after the record type, find its
      --position if so
      if EndIdx >= ZLength then
         Success := False;
      else
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         --don't bother checking if FoundType is a domainName, just take
         --whatever is there
         LengthOfToken := (EndIdx - BegIdx) + 1;
         if LengthOfToken > RR_Type.MaxDomainNameLength then
            Success := False;
            Error_Msgs.PrintDomainLengthErrorInfo (ZoneFileLine,
                                                   BegIdx,
                                                   EndIdx);
         else
            --have a domain name, but must still pad it
            for I in Integer range BegIdx .. EndIdx loop
               pragma Loop_Invariant
                 (BegIdx >= 1 and
                  EndIdx - BegIdx + 1 <= RR_Type.MaxDomainNameLength and
                  EndIdx = EndIdx'Loop_Entry);
               NewDomainName ((I + 1) - BegIdx) := ZoneFileLine (I);
            end loop;
            for I in Integer range EndIdx + 1.. RR_Type.MaxDomainNameLength loop
               -- Remind prover that EndIdx is in type
               pragma Loop_Invariant (EndIdx >= 1);
               NewDomainName(I) := ' ';
            end loop;
         end if;
      end if;
   end ParseDomainName;

   --for NSec records, just like ParseDomainName but also grabs character
   --string after it
   procedure ParseDomainNameAndRRString
     (NewDomainName :    out RR_Type.DomainNameStringType;
      RRString      :    out RR_Type.LineFromFileType;
      ZoneFileLine  : in     RR_Type.LineFromFileType;
      ZLength       : in     RR_Type.LineLengthIndex;
      Success       : in out Boolean)
   is
      BegIdx        : RR_Type.LineLengthIndex := 1;
      EndIdx        : RR_Type.LineLengthIndex;
      FoundType     : RR_Type.RRItemType;
      LengthOfToken : RR_Type.LineLengthIndex;

   begin
      RRString := RR_Type.BlankLine;
      NewDomainName := RR_Type.BlankDomainName;
      --find the record type indicator, which must be present since this
      --routine was called
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);

      --second condition always true if precondition of routine is met, but it
      --helps the prover
      while FoundType/= RR_Type.RecordIndicator and EndIdx < ZLength loop
         pragma Loop_Invariant (EndIdx < ZLength);
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
      end loop;

      --check to make sure something is after the record type, find its
      --position if so
      if EndIdx >= ZLength then
         Success := False;
      else
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         --don't bother checking if FoundType is a domainName, just take
         --whatever is there
         LengthOfToken := (EndIdx - BegIdx) + 1;
         if LengthOfToken > RR_Type.MaxDomainNameLength then
            Success := False;
            Error_Msgs.PrintDomainLengthErrorInfo (ZoneFileLine,
                                                   BegIdx,
                                                   EndIdx);
         else
            --have a domain name, but must still pad it
            for I in Integer range BegIdx .. EndIdx loop
               pragma Loop_Invariant
                 (BegIdx >= 1 and
                  EndIdx - BegIdx + 1 <= RR_Type.MaxDomainNameLength and
                  EndIdx = EndIdx'Loop_Entry);
               NewDomainName ((I + 1) - BegIdx) := ZoneFileLine (I);
            end loop;
            for I in Integer range EndIdx + 1 .. RR_Type.MaxDomainNameLength
            loop
               -- Remind prover that endIdx is in type
               pragma Loop_Invariant (EndIdx >= 1);
               NewDomainName(I) := ' ';
            end loop;
         end if;
         --this is the extra code for the RRString
         if EndIdx >= ZLength then
            Success := False;
         else
            BegIdx := EndIdx + 1;
            Parser_Utilities.FindNextToken (ZoneFileLine,
                                            ZLength,
                                            BegIdx,
                                            EndIdx,
                                            FoundType);
            --RRString is everything after the domain name to the end of the
            --line EndIdx := (EndIdx - EndIdx) + ZLength; --make flow error
            --go away
            LengthOfToken := (EndIdx - BegIdx) + 1;
            --for now, rrstring length max is same as domain name length max
            if LengthOfToken > RR_Type.MaxDomainNameLength then
               Success := False;
               Error_Msgs.PrintRRStringLengthErrorInfo (ZoneFileLine,
                                                        BegIdx,
                                                        EndIdx);
            else
            --have an RRString, but must still pad it
               for I in Integer range BegIdx .. EndIdx loop
                  pragma Loop_Invariant
                    (BegIdx >= 1 and
                     EndIdx - BegIdx + 1 <= RR_Type.MaxDomainNameLength and
                     EndIdx = EndIdx'Loop_Entry);
                  RRString ((I + 1) - BegIdx) := ZoneFileLine (I);
               end loop;
               for I in Integer range ((EndIdx + 2) - BegIdx) ..
                 RR_Type.LineLengthIndex'Last
               loop
                  -- Remind prover of postcondition from FindNextToken
                  pragma Loop_Invariant (EndIdx >= BegIdx);
                  RRString(I) := ' ';
            end loop;
         end if;
      end if;
   end if;
   END ParseDomainNameAndRRString;

   --Turn a string of record types (e.g. "A NS AAAA MX FOOBAR") into block
   --numbers and block lengths ready to go out on the wire.  See
   --http://tools.ietf.org/rfc/rfc3845.txt for details.
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
   is

      subtype BlockMapIndex is Unsigned_Types.Unsigned8 range 0..255;
      type BlockMapType is array (BlockMapIndex) of Boolean;
      type BlockLengthMapType is array (BlockMapIndex)
        of RR_Type.NSec_Record_Type.BlockLengthValue;

      BlockMap: BlockMapType := BlockMapType'(others => False);
      BlocklengthMap: BlockLengthMapType :=
        BlockLengthMapType'(others =>
                              RR_Type.NSec_Record_Type.BlockLengthValue'First);
      BegIdx : RR_Type.LineLengthIndex;
      EndIdx : RR_Type.LineLengthIndex;
      FoundType : RR_Type.RRItemType;
      RecordType : DNS_Types.Query_Type;
      BlockNumber : BlockMapIndex;
      BlockNumberOfFirstRecordType : BlockMapIndex;
      --helps convince SPARK that at least one block has been assigned
      BlockIndex : RR_Type.Nsec_Record_Type.BlockNumberValue;
      ByteNumber : RR_Type.NSec_record_type.BlockLengthValue;
      BitNumber : Natural;

      function From_Query_Type is new Ada.Unchecked_Conversion
        (DNS_Types.Query_Type, Unsigned_Types.Unsigned16);
   begin
      NumberOfRecordTypes := 0;
      RecordTypes := RR_Type.NSec_Record_Type.RecordTypeArrayType'(others => DNS_types.Unimplemented);
      NumberOfBlocks := 0;
      BlockNumbers := RR_Type.NSec_Record_Type.BlockNumberArrayType'(others => 0);
      BlockLengths := RR_Type.NSec_Record_Type.BlockLengthArrayType'(others => 1);
      BitMaps := RR_Type.NSec_Record_Type.BitMapsArrayArrayType'(others => RR_Type.NSec_Record_Type.BitMapArrayType'(others => 0));
      BegIdx := 1;

      Parser_Utilities.FindNextToken (RRString,
                                      RR_Type.MaxLineLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);
      --RRString must contain at least one record indicator or it's no good
      if FoundType /= RR_Type.RecordIndicator then
         Success := False;
      else   --build the block, block length and record type info
         --process the first record indicator
         RecordType := Parser_Utilities.GetRecordType (RRString,
                                                       BegIdx,
                                                       EndIdx);
         NumberOfRecordTypes := NumberOfRecordTypes + 1;
         RecordTypes (NumberOfRecordTypes) := RecordType;
         --blockNumber is the upper byte of RecordType
         BlockNumberOfFirstRecordType := BlockMapIndex ((From_Query_Type (RecordType)/256) mod 256);  --mod for SPARK only
         BlockMap (BlockNumberOfFirstRecordType) := True;
	 NumberOfBlocks := NumberOfBlocks + 1;
         --helps prove postcondition to count this block here

         --byte number is the upper 5 bits of the lower byte of RecordType,
         --plus 1
         ByteNumber := RR_Type.NSec_Record_Type.BlockLengthValue
           ((((From_Query_Type (RecordType) - 256*(From_Query_Type (RecordType)/256))/8) mod 32) + 1); --mod for SPARK only
         BlockLengthMap (BlockNumberOfFirstRecordType) := ByteNumber;

         --second condition always true if precondition of routine is met, but
         --it helps the prover
         while FoundType = RR_Type.RecordIndicator and
           EndIdx < RR_Type.MaxLineLength and
           NumberOfRecordTypes <
             Rr_Type.Nsec_Record_Type.MaxNumberOfRecordTypes
         loop
            pragma Loop_Invariant
              (EndIdx >= 0 and
               EndIdx < RR_Type.MaxLineLength and
               NumberOfRecordTypes >= 1 and
               NumberOfRecordTypes <
                 RR_Type.NSec_Record_Type.MaxNumberOfRecordTypes and
               NumberOfBlocks = 1 and
               (for all J in BlockMapIndex =>
                  BlockLengthMap(J) >=
                    Rr_Type.Nsec_Record_Type.blockLengthValue'first and
                  BlockLengthMap(J) <=
                    Rr_Type.Nsec_Record_Type.blockLengthValue'Last));
            --above three lines are needed for later loops
            Parser_Utilities.FindNextToken (RRString,
                                            RR_Type.MaxLineLength,
                                            BegIdx,
                                            EndIdx,
                                            FoundType);
            if FoundType = RR_Type.RecordIndicator then
               RecordType := Parser_Utilities.GetRecordType (RRString,
                                                             BegIdx,
                                                             EndIdx);
               NumberOfRecordTypes := NumberOfRecordTypes + 1;
               RecordTypes (NumberOfRecordTypes) := RecordType;
               --BlockNumber is the upper byte of RecordType
               BlockNumber :=
                 BlockMapIndex ((From_Query_Type (RecordType)/256) mod 256);
               --mod for SPARK only

               BlockMap (BlockNumber) := True;
               --may have already been set, doesn't matter

               --byte number is the upper 5 bits of the lower byte of
               --RecordType, plus 1
               ByteNumber := RR_Type.NSec_Record_Type.BlockLengthValue
                 ((((From_Query_Type (RecordType) - 256*(From_Query_Type (RecordType)/256))/8) mod 32) + 1); --mod for SPARK only
               if ByteNumber > BlockLengthMap (BlockNumber) then
                  BlockLengthMap (BlockNumber) := ByteNumber;
               end if;
            end if;
         end loop;
         --check if any remaining record types, display a warning if so
         if NumberOfRecordTypes =
              RR_Type.NSec_Record_Type.MaxNumberOfRecordTypes and
           EndIdx < RR_Type.MaxLineLength
         then
            Error_Msgs.PrintTooManyRecordTypesInNSecRecordWarning (LineCount);
         end if;

         --collapse the block and block length maps into the actual fields of
         --the record need to remind the prover of a couple of things first

         pragma Assert
           (NumberOfBlocks = 1 and
            (for all J in BlockMapIndex =>
               BlockLengthMap (J) >=
                 RR_Type.Nsec_Record_Type.blockLengthValue'First and
               BlockLengthMap (J) <=
                 RR_Type.Nsec_Record_Type.blockLengthValue'Last) and
            NumberOfRecordTypes >= 1 and
            NumberOfRecordTypes <=
              RR_Type.NSec_Record_Type.MaxNumberOfRecordTypes);
      	 for I in BlockMapIndex loop

            pragma Loop_Invariant
              (NumberOfBlocks >= 1 and
               NumberOfBlocks < RR_Type.NSec_Record_Type.MaxNumberOfBlocks and
               (for all J in BlockMapIndex =>
                  (BlockLengthMap(J) >=
                     RR_Type.NSec_Record_Type.BlockLengthValue'First and
                   BlockLengthMap(J) <=
                     RR_Type.NSec_Record_Type.BlockLengthValue'Last)) and
               NumberOfRecordTypes >= 1 and
               NumberOfRecordTypes <=
                 RR_Type.NSec_Record_Type.MaxNumberOfRecordTypes);
            if BlockMap (I) and I /= BlockNumberOfFirstRecordType then
               --block of first record type already counted
               NumberOfBlocks := NumberOfBlocks + 1;
               BlockNumbers (NumberOfBlocks) := DNS_Types.Byte (I);
               BlockLengths (NumberOfBlocks) := BlockLengthMap (I);
            end if;

            --this is redundant, since if NumberOfBlocks hits its maximum value
            --then all the remaining entries in BlockMap will be false, but
            --convincing SPARK that NumberOfBlocks remains in type is too
            --painful
            exit when NumberOfBlocks =
                        RR_Type.NSec_Record_Type.MaxNumberOfBlocks;
         end loop;

         --Finally, set the bitmaps
         --remind the prover of what it should know
         pragma Assert
           (NumberOfRecordTypes >= 1 and
            NumberOfRecordTypes <=
              RR_Type.NSec_Record_Type.MaxNumberOfRecordTypes and
            NumberOfBlocks >= 1 and
            NumberOfBlocks <=
              RR_Type.NSec_Record_Type.BlockNumberArrayIndex'Last);
         BitMaps :=
           RR_Type.NSec_Record_Type.BitMapsArrayArrayType'(others =>
             RR_Type.NSec_Record_Type.BitMapArrayType'(others => 0));
         --helps prover

         for I in RR_Type.NSec_Record_Type.RecordTypeIndexValue
           range 1 .. NumberOfRecordTypes
         loop
            pragma Loop_Invariant
              (NumberOfRecordTypes >= 1 and
               NumberOfRecordTypes <=
                 RR_Type.NSec_Record_Type.MaxNumberOfRecordTypes and
               NumberOfBlocks >= 1 and
               NumberOfBlocks <=
                 RR_Type.NSec_Record_Type.BlockNumberArrayIndex'last);
            BlockIndex := 1;	--makes flow error go away
            for J in RR_Type.NSec_Record_Type.BlockNumberValue
              range 1 .. NumberOfBlocks
            loop
               pragma Loop_Invariant
                 (NumberOfRecordTypes >= 1 and
                  NumberOfRecordTypes <=
                    RR_Type.NSec_Record_Type.MaxNumberOfRecordTypes and
                  NumberOfBlocks >= 1 and
                  NumberOfBlocks <=
                    RR_Type.NSec_Record_Type.BlockNumberArrayIndex'Last and
                  BlockIndex >=
                    RR_Type.NSec_Record_Type.BlockNumberArrayIndex'First and
                  BlockIndex <=
                    RR_Type.NSec_Record_Type.BlockNumberArrayIndex'Last);
               if BlockNumbers (J) =
                 DNS_Types.Byte ((From_Query_Type (RecordTypes (I))/256) mod 256)
               then ----mod for SPARK only
                  BlockIndex := J;
                  exit;
               end if;
            end loop;
            ByteNumber := Rr_Type.Nsec_Record_Type.BlockLengthValue
              ((((From_Query_Type(RecordType) - 256*(From_Query_Type(RecordType)/256))/8) mod 32) + 1);
            --mod for SPARK only

            BitNumber := Natural (From_Query_Type(RecordTypes(I)) mod 8);
            --bytes in a byte are indexed from 0, left to right

            BitMaps (BlockIndex)(ByteNumber) :=
              BitMaps (BlockIndex)(ByteNumber) + 2**(7-BitNumber);
         end loop;
      end if;	--RRString has at least one record type
   END FillBlockInfo;

   procedure ParseTimeSpec
     (NewTimeSpec  :    out Unsigned_Types.Unsigned32;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      BegIdx    : RR_Type.LineLengthIndex := 1;
      EndIdx    : RR_Type.LineLengthIndex;
      FoundType : RR_Type.RRItemType;
   begin
      NewTimeSpec := 0;
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);

      --next token must be a time specifier or number, otherwise error
      if FoundType /= RR_Type.DomainNameOrTimeSpec and
        FoundType /= RR_Type.Number
      then
         Success := False;
      else
         Parser_Utilities.ConvertTimeSpec (ZoneFileLine,
                                           BegIdx,
                                           EndIdx,
                                           NewTimeSpec,
                                           Success);
      end if;  --number found?
   end ParseTimeSpec;

   procedure ParseControlLine
     (NewOrigin    : in out RR_Type.DomainNameStringType;
      NewTTL       : in out Unsigned_Types.Unsigned32;
      zoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      BegIdx    : RR_Type.LineLengthIndex := 1;
      EndIdx    : RR_Type.LineLengthIndex;
      FoundType : RR_Type.RrItemType;
      TmpLine   : RR_type.LineFromFileType :=
        RR_Type.LineFromFileType'(others => ' ');
   begin

      --find the control command, which must be present since this routine was
      --called
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);
      if FoundType = RR_Type.Control then --should always be true
         --only $TTL and $ORIGIN currently recognized
         --phrasing conditions this way helps the prover
         if BegIdx <= EndIdx - 6 then --$ORIGIN?
            if ZoneFileline (BegIdx + 1) = 'O' and
               ZoneFileline (BegIdx + 2) = 'R' and
               ZoneFileline (BegIdx + 3) = 'I' and
               ZoneFileline (BegIdx + 4) = 'G' and
               ZoneFileline (BegIdx + 5) = 'I' and
               ZoneFileline (BegIdx + 6) = 'N'
            then
               if BegIdx < ZLength and EndIdx < ZLength then
                  BegIdx := EndIdx + 1;
                  Parser_Utilities.FindNextToken (ZoneFileLine,
                                                  ZLength,
                                                  BegIdx,
                                                  EndIdx,
                                                  FoundType);
               end if;
               if FoundType /= RR_Type.DomainNameOrTimeSpec then
                  Success := False;
               elsif ZoneFileLine (EndIdx) /= '.' then
                  Success := False;   --argument to $ORIGIN must end with '.'
               else
                  --create a line with a dummy record indicator and the domain
                  --name so it can be parsed with ParseDomainName
                  for I in Integer range BegIdx .. EndIdx loop
                     pragma Loop_Invariant (BegIdx >= 1 and BegIdx <= EndIdx);
                     TmpLine(I) := ZoneFileLine(I);
                  end loop;
                  --we know the domain name can't start before pos 6,
                  --so this will work
                  TmpLine(1) := 'A';
                  ParseDomainName (NewOrigin,
                                   TmpLine,
                                   RR_Type.MaxLineLength,
                                   Success);
               end if;
            else
               Success := False;
            end if;  --control token of length 6
         elsif BegIdx <= EndIdx - 3 then --$TTL?
            if ZoneFileline (BegIdx + 1) = 'T' and
               ZoneFileline (BegIdx + 2) = 'T' and
               ZoneFileline (BegIdx + 3) = 'L'
            then
               if BegIdx < ZLength and EndIdx < ZLength then
                  Begidx := EndIdx + 1;
                  Parser_Utilities.FindNextToken (ZoneFileLine,
                                                  ZLength,
                                                  BegIdx,
                                                  EndIdx,
                                                  FoundType);
               end if;
               if FoundType /= RR_Type.DomainNameOrTimeSpec and
                 FoundType /= RR_Type.Number
               then
                  Success := False;
               else
                  --create a line with only the time spec on it so it can be
                  --parsed with ParseTimeSpec
                  for I in Integer range BegIdx .. EndIdx loop
                     TmpLine (I) := ZoneFileLine (I);
                  end loop;
                  ParseTimeSpec (NewTTL,
                                 TmpLine,
                                 RR_Type.MaxLineLength,
                                 Success);
               end if;
            else
               Success := False;
            end if;  --control token of length 3

         end if; --$TTL or $ORIGIN
      else
         Success := False;
      end if; --whether or not control token found
   end ParseControlLine;

   procedure ParseSerialNumber
     (NewSerialNumber :    out Unsigned_Types.Unsigned32;
      ZoneFileLine    : in     RR_Type.LineFromFileType;
      ZLength         : in     RR_Type.LineLengthIndex;
      Success         : in out Boolean)
   is
      BegIdx    : RR_Type.LineLengthIndex := 1;
      EndIdx    : RR_Type.LineLengthIndex;
      FoundType : RR_Type.RRItemType;
      DigitVal  : Unsigned_Types.Unsigned32;
      TmpVal    : Long_Long_Integer;

   begin
      NewSerialNumber := 0;

      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);

      --next token must be a number, otherwise error
      if FoundType /= RR_Type.Number then
         Success := False;
      else
         TmpVal := 0;
         for I in integer range BegIdx .. EndIdx loop
            pragma Loop_Invariant
              (BegIdx >= 1 and
               TmpVal >= 0 and
               TmpVal <= RR_Type.SOA_Record_Type.Max_Serial_Val);
            DigitVal := Character'Pos (ZoneFileLine (I)) - Character'Pos('0');
            TmpVal := 10 * TmpVal + Long_Long_Integer (DigitVal);
            --bail out early if serial# is too large
            exit when TmpVal > RR_Type.SOA_Record_Type.Max_Serial_Val;
         end loop;
         --make sure it's not too big
         if TmpVal > RR_Type.SOA_Record_Type.Max_Serial_Val then
            Success := False;
         else --have a valid serial number
            NewSerialNumber := Unsigned_Types.Unsigned32 (TmpVal);
         end if;  --too large pref?
      end if;  --number found?
   end ParseSerialNumber;

   --precondition is that zoneFileLine contains a record indicator
   --Data item after "MX" record indicator should be a valid 16-bit integer
   procedure ParsePrefandDomainName
     (NewPref       :    out Unsigned_Types.Unsigned16;
      NewDomainName :    out RR_Type.DomainNameStringType;
      ZoneFileLine  : in     RR_Type.LineFromFileType;
      ZLength       : in     RR_Type.LineLengthIndex;
      Success       : in out Boolean)
   is
      BegIdx        : RR_Type.LineLengthIndex := 1;
      EndIdx        : RR_Type.LineLengthIndex;
      FoundType     : RR_Type.RRItemType;
      DigitVal      : Unsigned_Types.Unsigned16;
      TmpVal        : Unsigned_Types.Unsigned16;
      LengthOfToken : RR_Type.LineLengthIndex;

   begin
      NewPref := 0;
      NewDomainName := RR_Type.BlankDomainName;

      --find the record type indicator, which must be present since this
      --routine was called
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);

      --second condition always true if precondition of routine is met, but it
      --helps the prover
      while FoundType/= RR_Type.RecordIndicator and EndIdx < ZLength loop
         pragma Loop_Invariant (EndIdx < ZLength);
         BegIdx := endIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
      end loop;

      --check to make sure something is after the record type, find its
      --position if so
      if EndIdx = ZLength then
         Success := False;
      else
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         if FoundType /= RR_Type.Number then
            Success := False;
         else --convert token to number
            TmpVal := 0;
            for I in Integer range BegIdx .. EndIdx loop
               pragma Loop_Invariant
                 (BegIdx >= 1 and
                  TmpVal <= RR_Type.MX_Record_Type.Max_Pref_Val);
               DigitVal :=
                 Character'Pos (ZoneFileLine (I)) - Character'Pos('0');
               TmpVal := 10 * TmpVal + DigitVal;
               exit when TmpVal > RR_Type.MX_Record_Type.Max_Pref_Val;
            end loop;
            --make sure it's not too big
            if TmpVal > RR_Type.MX_Record_Type.Max_Pref_Val then
               Success := False;
            else --have a valid preference value
               NewPref := TmpVal;
               --next token must be a domain name
               if EndIdx >= ZLength then  -- use of ">=" helps the prover
                  Success := False;
               else
                  BegIdx := EndIdx + 1;
         	  Parser_Utilities.FindNextToken (ZoneFileLine,
                                                  ZLength,
                                                  BegIdx,
                                                  EndIdx,
                                                  FoundType);
         	  LengthOfToken := (EndIdx - BegIdx) + 1;
         	  if FoundType /= RR_Type.DomainNameorTimeSpec then
            	     Success := False;
         	  elsif LengthOfToken > RR_Type.MaxDomainNameLength then
            	     Success := False;
            	     Error_Msgs.PrintDomainLengthErrorInfo (ZoneFileLine,
                                                            BegIdx,
                                                            EndIdx);
         	  else
            	     --have a domain name, but must still pad it
            	     for I in Integer range BegIdx .. EndIdx loop
                        pragma Loop_Invariant
                          (BegIdx >= 1 and
                           EndIdx - BegIdx + 1 <=
                             RR_Type.MaxDomainNameLength and
                           EndIdx = EndIdx'Loop_Entry);
               		NewDomainName ((I + 1) - BegIdx) := ZoneFileLine (I);
            	     end loop;
            	     for I in Integer range
                       EndIdx + 1.. RR_Type.MaxDomainNameLength
                     loop
               		-- Remind prover that endIdx is in type
                        pragma Loop_Invariant (EndIdx >= 1);
               		NewDomainName(I) := ' ';
            	     end loop;
                  end if;  --valid domain name?
               end if;  --end of string reached after preference value?
            end if;  --too large pref?
         end if;  --number found?
      end if;  --end of string reached after record indicator?
   end ParsePrefAndDomainName;


   --precondition is that ZoneFileLine contains a record indicator
   --Data item after "SRV" record indicator should be a valid 16-bit integer
   procedure ParsePrefWeightPortAndDomainName
     (NewPref       :    out Unsigned_Types.Unsigned16;
      NewWeight     :    out Unsigned_Types.Unsigned16;
      NewPort       :    out Unsigned_Types.Unsigned16;
      NewDomainName :    out RR_Type.DomainNameStringType;
      ZoneFileLine  : in     RR_Type.LineFromFileType;
      ZLength       : in     RR_Type.LineLengthIndex;
      Success       : in out Boolean)
   is
      BegIdx        : RR_Type.LineLengthIndex := 1;
      EndIdx        : RR_Type.LineLengthIndex;
      FoundType     : RR_Type.RRItemType;
      DigitVal      : Unsigned_Types.Unsigned16;
      TmpVal        : Unsigned_Types.Unsigned16;
      LengthOfToken : RR_Type.LineLengthIndex;
   begin
      NewPref := 0;
      NewWeight := 0;
      NewPort := 0;
      NewDomainName := RR_Type.BlankDomainName;

      --find the record type indicator, which must be present since this
      --routine was called
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);

      --second condition always true if precondition of routine is met, but it
      --helps the prover
      while FoundType/= RR_Type.RecordIndicator and EndIdx < ZLength loop
         pragma Loop_Invariant (EndIdx < ZLength);
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
      end loop;

      --check to make sure something is after the record type, find its
      --position if so
      if EndIdx = ZLength then
         Success := False;
      else
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         if FoundType /= RR_Type.Number then
            Success := False;
         ELSE --convert token to number
            TmpVal := 0;
            for I in Integer range BegIdx .. EndIdx loop
               pragma Loop_Invariant
                 (BegIdx >= 1 and
                  TmpVal <= RR_Type.Srv_Record_Type.Max_Pref_Val);
               DigitVal := Character'Pos (ZoneFileLine (I)) -
                             Character'Pos('0');
               TmpVal := 10 * TmpVal + DigitVal;
               exit when TmpVal > RR_Type.Srv_Record_Type.Max_Pref_Val;
            end loop;
            --make sure it's not too big
            if TmpVal > RR_Type.Srv_Record_Type.Max_Pref_Val then
               Success := False;
            else --have a valid preference value
               NewPref := TmpVal;
               if EndIdx >= ZLength then  -- use of ">=" helps the prover
                  success := false;

               --next token must be weight
               else
                  BegIdx := EndIdx + 1;
                  Parser_Utilities.FindNextToken (ZoneFileLine,
                                                  ZLength,
                                                  BegIdx,
                                                  EndIdx,
                                                  FoundType);
                  if FoundType /= RR_Type.Number then
                     Success := False;
                  else --convert token to number
                     TmpVal := 0;
                     for I in Integer range BegIdx .. EndIdx loop
                        pragma Loop_Invariant
                          (BegIdx >= 1 and
                           TmpVal <= RR_Type.Srv_Record_Type.Max_Weight_Val);
                        DigitVal :=
                          Character'Pos (ZoneFileLine (I)) - Character'Pos('0');
                        TmpVal := 10 * TmpVal + DigitVal;
                        exit when TmpVal >
                                    RR_Type.Srv_Record_Type.Max_Weight_Val;
                     end loop;
                     --make sure it's not too big
                     if TmpVal > RR_Type.Srv_Record_Type.Max_Weight_Val then
                        Success := False;
                     else --have a valid weightvalue
                        NewWeight := TmpVal;
                        if EndIdx >= ZLength then
                           -- use of ">=" helps the prover
                           Success := False;

                        --next token must be port
                        else
                           BegIdx := EndIdx + 1;
                           Parser_Utilities.FindNextToken (ZoneFileLine,
                                                           ZLength,
                                                           BegIdx,
                                                           EndIdx,
                                                           FoundType);
                           if FoundType /= RR_Type.Number then
                              success := False;
                           else --convert token to number
                              TmpVal := 0;
                              for I in Integer range BegIdx .. EndIdx loop
                                 pragma Loop_Invariant
                                   (BegIdx >= 1 and
                                    TmpVal <=
                                      RR_Type.Srv_Record_Type.Max_Port_Val);
                                 DigitVal :=
                                   Character'Pos (ZoneFileLine (I)) -
                                   Character'Pos ('0');
                                 TmpVal := 10 * TmpVal+ DigitVal;
                                 exit when TmpVal >
                                   RR_Type.Srv_Record_Type.Max_Port_Val;
                              end loop;
                              --make sure it's not too big
                              if TmpVal > RR_Type.Srv_Record_Type.Max_Port_Val
                              then
                                 Success := False;
                              else --have a valid weightvalue
                                 NewPort := TmpVal;
                                 if EndIdx >= ZLength then
                                    -- use of ">=" helps the prover
                                    Success := False;

                                 --next token must be a domain name
                                 else
                                    BegIdx := EndIdx + 1;
                              	    Parser_Utilities.FindNextToken
                                      (ZoneFileLine,
                                       ZLength,
                                       BegIdx,
                                       EndIdx,
                                       FoundType);
                                    LengthOfToken := (EndIdx - BegIdx) + 1;
                               	    if FoundType /=
                                      RR_Type.DomainNameorTimeSpec
                                    then
                                       Success := False;
                              	    elsif LengthOfToken >
                                      RR_Type.MaxDomainNameLength
                                    then
                                       Success := False;
                                       Error_Msgs.PrintDomainLengthErrorInfo
                                         (ZoneFileLine,
                                          BegIdx,
                                          EndIdx);
                              	    else
                                       --have a domain name, but must still pad it
                                       for I in Integer
                                         range BegIdx .. EndIdx
                                       loop
                                          pragma Loop_Invariant
                                            (BegIdx >= 1 and
                                             EndIdx - BegIdx + 1 <=
                                               RR_Type.MaxDomainNameLength and
                                             EndIdx = EndIdx'Loop_Entry);
                                          NewDomainName ((I + 1) - BegIdx) :=
                                            ZoneFileLine (I);
                                       end loop;
                                       for I in Integer range
                                         EndIdx + 1 .. RR_Type.MaxDomainNameLength
                                       loop
                                          -- Remind prover that endIdx is in type
                                          pragma Loop_Invariant (EndIdx >= 1);
                                          NewDomainName(I) := ' ';
                              	      end loop;
                                    end if;  --valid domain name?
                                 end if;  --end of string reached after portvalue?
                              end if;  --too large port?
                           end if;  --number found?
                        end if;  --end of string reached after weight value?
                     end if;  --too large weight?
                  end if;  --number found?
               end if;  --end of string reached after preference value?
            end if;  --too large pref?
         end if;  --number found?
      end if;  --end of string reached after record indicator?
   end ParsePrefWeightPortAndDomainName;


   procedure ParseIPV4
     (NewIPV4      :    out Unsigned_types.Unsigned32;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      BegIdx    : RR_Type.LineLengthIndex := 1;
      EndIdx    : RR_Type.LineLengthIndex;
      FoundType : RR_Type.RRItemType;
      TmpVal    : Unsigned_Types.Unsigned32;

   begin
      NewIPV4 := 0;
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);
      --loop until you find an IPV4
      while FoundType /= RR_Type.IPV4 and EndIdx < ZLength loop
         pragma Loop_Invariant (EndIdx < ZLength);
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
      end loop;

      if FoundType /= RR_Type.IPV4 and EndIdx >= ZLength then	-- ">=" helps the prover
         Success := False;
      else
         TmpVal := Parser_Utilities.ConvertIPV4 (ZoneFileLine,
                                                 BegIdx,
                                                 EndIdx);
         if TmpVal = 0 then
            Success := False;
         else
            NewIPV4 := TmpVal;
         end if;
      end if;
   end ParseIPV4;

   procedure ParseIPV6
     (NewIPV6      :    out RR_Type.AAAA_Record_Type.IPV6AddrType;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      BegIdx    : RR_Type.LineLengthIndex := 1;
      EndIdx    : RR_Type.LineLengthIndex;
      FoundType : RR_Type.RRItemType;

   begin
      NewIPV6 := RR_Type.AAAA_Record_Type.Invalid_IPV6_Addr;
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);

      --loop until you find an IPV6
      while FoundType /= RR_Type.IPV6 and EndIdx < ZLength loop
         pragma Loop_Invariant (EndIdx < ZLength);
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
      end loop;

      if FoundType /= RR_Type.IPV6 and EndIdx >= ZLength then	-- ">=" helps the prover
         Success := False;
      else
         NewIPV6 := Parser_Utilities.ConvertIPV6 (ZoneFileLine,
                                                  BegIdx,
                                                  EndIdx);
         if NewIPV6 = RR_Type.AAAA_Record_Type.Invalid_IPV6_Addr then
            Success := False;
         end if;
      end if;
   end ParseIPV6;

   --precondition is that zoneFileLine contains a record indicator, but can't
   --express that in SPARK
   --Basically like parseDomainName done twice
   procedure ParseNameServerAndEmail
     (NewNameServer :    out RR_Type.DomainNameStringType;
      NewEmail      :    out RR_Type.DomainNameStringType;
      ZoneFileLine  : in     RR_Type.LineFromFileType;
      ZLength       : in     RR_Type.LineLengthIndex;
      Success       : in out Boolean)
   is
      BegIdx        : RR_Type.LineLengthIndex := 1;
      EndIdx        : RR_Type.LineLengthIndex;
      FoundType     : RR_Type.RRItemType;
      LengthOfToken : RR_Type.LineLengthIndex;

   BEGIN
      NewNameServer := RR_Type.BlankDomainName;
      NewEmail := RR_Type.BlankDomainName;
      --find the record type indicator, which must be present since this
      --routine was called
      Parser_Utilities.FindNextToken (ZoneFileLine,
                                      ZLength,
                                      BegIdx,
                                      EndIdx,
                                      FoundType);

      --second condition always true if precondition of routine is met, but it
      --helps the prover
      while FoundType/= RR_Type.RecordIndicator and EndIdx < ZLength loop
         pragma Loop_Invariant (EndIdx < ZLength);
         BegIdx := EndIdx + 1;  --makes flow error go away
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
      end loop;

      --check to make sure something is after the record type, find its
      --position if so
      if EndIdx >= ZLength then
         Success := False;
      else
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         LengthOfToken := (EndIdx - begIdx) + 1;
         if FoundType /= RR_Type.DomainNameOrTimeSpec then
            Success := False;
         elsif LengthOfToken > Rr_Type.MaxDomainNameLength then
            Success := False;
            Error_Msgs.PrintDomainLengthErrorInfo (ZoneFileLine,
                                                   BegIdx,
                                                   EndIdx);
         else
            --have a domain name, but must still pad it
            for I in Integer range BegIdx .. EndIdx loop
               pragma Loop_Invariant
                 (BegIdx >= 1 and
                  EndIdx - BegIdx + 1 <= RR_Type.MaxDomainNameLength and
                  EndIdx = EndIdx'Loop_Entry);
               NewNameServer ((I + 1) - BegIdx) := ZoneFileLine (I);
            end loop;
            for I in Integer range EndIdx + 1.. RR_Type.MaxDomainNameLength loop
               -- Remind prover that endIdx is in type
               pragma Loop_Invariant (EndIdx >= 1);
               NewNameServer(I) := ' ';
            end loop;
         end if;

      end if;

      --do it all again to get the email
      --check to make sure something is after the name server, find its
      --position if so
      if EndIdx >= ZLength then
         Success := False;
      else
         BegIdx := EndIdx + 1;
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         FoundType);
         LengthOfToken := (EndIdx - BegIdx) + 1;
         if FoundType /= RR_Type.DomainNameOrTimeSpec then
            Success := False;
         elsif LengthOfToken > RR_Type.MaxDomainNameLength then
            Success := False;
            Error_Msgs.PrintDomainLengthErrorInfo (ZoneFileLine,
                                                   BegIdx,
                                                   EndIdx);
         else
            --have a domain name, but must still pad it
            for I in Integer range BegIdx .. EndIdx loop
               pragma Loop_Invariant
                 (BegIdx >= 1 and
                  EndIdx - BegIdx + 1 <=
                    RR_Type.MaxDomainNameLength and
                  EndIdx = EndIdx'Loop_Entry);
               NewEmail ((I + 1) - BegIdx) := ZoneFileLine (I);
            end loop;
            for I in Integer
              range EndIdx + 1 .. RR_Type.MaxDomainNameLength
            loop
               -- Remind prover that endIdx is in type
               pragma Loop_Invariant (EndIdx >= 1);
               NewEmail (I) := ' ';
            end loop;
         end if;
      end if;
   end ParseNameServerAndEmail;

   --domain name, TTL and class on a line are all optional, if blank default to
   --last known values
   --succeeds if a record type is found
   procedure ParseOwnerTTLClassAndRecordType
     (NewOwner     : in out RR_Type.DomainNameStringType;
      NewTTL       : in out Unsigned_Types.Unsigned32;
      NewClass     : in out RR_Type.ClassType;
      NewType      : in out DNS_Types.Query_Type;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      ZLength      : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      BegIdx          : RR_Type.LineLengthIndex := 1;
      EndIdx          : RR_Type.LineLengthIndex;
      Token           : RR_Type.LineFromFileType :=
        RR_Type.LineFromFileType'(others => ' ');
      LengthOfToken   : RR_Type.LineLengthIndex;
      TokenType       : RR_Type.RrItemType;
      RecordTypeFound : boolean := false;
      FirstChar       : Character;
      LastChar        : Character;

   begin
      --if 1st char isn't blank, then first token is a domainName regardless of
      --returned value of TokenType
      if ZoneFileLine (1) /= ' ' and
        ZoneFileLine (1) /= Ada.Characters.Latin_1.HT
      then
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         TokenType);
         LengthOfToken := (EndIdx - BegIdx) + 1;
         for I in Integer range BegIdx .. EndIdx loop
            pragma Loop_Invariant (BegIdx >= 1 and BegIdx <= EndIdx);
            Token ((I + 1) - BegIdx) := ZoneFileLine (i);
         end loop;
         if LengthOfToken >= RR_Type.MaxDomainNameLength then
            Success := False;
            Error_Msgs.PrintDomainLengthErrorInfo (ZoneFileLine,
                                                   BegIdx,
                                                   EndIdx);
         else
            NewOwner := RR_Type.BlankDomainName;
            --in case previous owner longer than new one
            for I in Integer range 1 .. LengthOfToken loop
               pragma Loop_Invariant
                 (LengthOfToken = LengthOfToken'Loop_Entry and
                  LengthOfToken < RR_Type.MaxDomainNameLength);
               NewOwner (I) := Token (I);
            end loop;
         end if;
         --line must contain a record type or the parse fails
         --use of ">=" helps the prover
         if EndIdx >= ZLength or TokenType = RR_Type.Comment then
            Success := False;
      	 else
	    BegIdx := EndIdx + 1;
         end if;
      end if;

      --now keep going until you find a record type, which will be present in
      --every valid record in the file
      while not RecordTypeFound and Success loop
         Parser_Utilities.FindNextToken (ZoneFileLine,
                                         ZLength,
                                         BegIdx,
                                         EndIdx,
                                         TokenType);
         --postcondition from findNextToken()
         pragma Loop_Invariant (BegIdx <= EndIdx);
         for I in Integer range BegIdx .. EndIdx loop
            pragma Loop_Invariant (BegIdx >= 1 and BegIdx <= EndIdx);
            Token ((I + 1) - BegIdx) := ZoneFileLine (I);
         end loop;
         case TokenType is
            when RR_Type.Number | Rr_Type.DomainNameOrTimeSpec =>
               Parser_Utilities.ConvertTimeSpec (ZoneFileLine,
                                                 BegIdx,
                                                 EndIdx,
                                                 NewTTL,
                                                 Success);
            when Rr_Type.Class =>
               FirstChar := Ada.Characters.Handling.To_Upper (Token(BegIdx));
               LastChar := Ada.Characters.Handling.To_Upper (Token(EndIdx));
               if FirstChar = 'C' and LastChar = 'H' then
                  NewClass := RR_Type.CH;
               elsif FirstChar = 'C' and LastChar = 'S' then
                  NewClass := RR_Type.CS;
               elsif FirstChar = 'H' and LastChar = 'S' then
                  NewClass := RR_Type.HS;
               elsif FirstChar = 'I' and LastChar = 'N' then
                  NewClass := RR_Type.Internet;
               end if;
            when RR_Type.RecordIndicator =>
               RecordTypeFound := True;
               --this means we have found a valid record type indicator
               NewType := Parser_Utilities.GetRecordType (ZoneFileLine,
                                                          BegIdx,
                                                          EndIdx);
            when others =>
               Success := False;
	    end case;

        --line must contain a record type or the parse fails
        --use of ">=" helps the prover
        if EndIdx >= ZLength or TokenType = RR_Type.Comment then
           if not RecordTypeFound then
              Success := False;
           end if;
      	 else
            BegIdx := EndIdx + 1;
        end if;
      end loop; --while record type token not found and line still has tokens
   end ParseOwnerTTLCLassAndRecordType;

end Zone_File_Parser;
