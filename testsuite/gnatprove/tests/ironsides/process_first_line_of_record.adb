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

with DNS_Table_Pkg,
     Zone_File_Parser,
     Error_Msgs,
     Parser_Utilities,
     RR_Type.A_Record_Type,
     RR_Type.AAAA_Record_Type,
     RR_Type.CName_Record_Type,
     RR_Type.Mx_Record_Type,
     RR_Type.Srv_Record_Type,
     RR_Type.NS_Record_Type,
     RR_Type.NSec_Record_Type,
     RR_Type.Ptr_Record_Type;

--just in case debugging needed
--WITH Ada.Text_IO, Ada.Integer_Text_IO;

package body Process_First_Line_Of_Record is
   --had to encapsulate this in a separate procedure to help the examiner
   --lots of parameters because of line-oriented file processing, different
   --kinds of parameters and multiline records require large amount of state
   --to persist across procedure calls
   procedure ProcessFirstLineOfRecord
     (CurrentRecordType          : in      DNS_Types.Query_Type;
      --common to all record types
      CurrentOrigin              : in      RR_Type.DomainNameStringType;
      CurrentOwner               : in      RR_Type.DomainNameStringType;
      CurrentTTL                 : in      Unsigned_types.Unsigned32;
      CurrentClass               : in      RR_Type.ClassType;
      CurrentLine                : in      RR_Type.LineFromFileType;
      LastPos                    : in      RR_Type.Linelengthindex;
      LineCount                  : in      Unsigned_Types.Unsigned32;
      --for multiline records
      InMultilineRecord          :     out Boolean;
      LineInRecordCtr            :     out Unsigned_Types.Unsigned32;
      --SOA record fields
      CurrentNameServer          :     out RR_Type.DomainNameStringType;
      CurrentEmail               :     out RR_Type.DomainNameStringType;
      --DNSKey record (if needed)
      DNSKey_Rec                 :     out RR_Type.Dnskey_Record_Type.DNSKeyRecordType;
      --RRSig record (if needed)
      RRSig_Rec                  :    out RR_Type.RRSig_Record_Type.RRSigRecordType;
      RecordSuccessfullyInserted :    out Boolean;
      Success                    : in out boolean)
   is
      CurrentIPV4         : Unsigned_Types.Unsigned32;
      CurrentIPV6         : RR_Type.AAAA_Record_Type.IPV6AddrType;
      CurrentDomainName   : RR_Type.DomainNameStringType;
      CurrentPref         : Unsigned_Types.Unsigned16;
      CurrentWeight       : Unsigned_Types.Unsigned16;
      CurrentPort         : Unsigned_Types.Unsigned16;
      RRString            : RR_Type.LineFromFileType;
      NumberOfBlocks      : RR_Type.NSec_Record_Type.BlockNumberValue;
      NumberOfRecordTypes : RR_Type.NSec_Record_Type.RecordTypeIndexValue;
      RecordTypes         : RR_Type.NSec_Record_Type.RecordTypeArrayType;
      BlockNumbers        : RR_Type.NSec_Record_Type.BlockNumberArrayType;
      BlockLengths        : RR_Type.NSec_Record_Type.BlockLengthArrayType;
      BitMaps             : RR_Type.NSec_Record_Type.BitMapsArrayArrayType;
   begin
      --these assignments all make bogus flow errors go away
      InMultilineRecord := False;
      LineInRecordCtr := 0;
      CurrentNameServer := RR_Type.BlankDomainName;
      CurrentEmail := RR_Type.BlankDomainName;
      DNSKey_Rec := RR_Type.DNSKey_Record_Type.BlankDNSKeyRecord;
      RRSig_Rec := RR_Type.RRSig_Record_Type.BlankRRSigRecord;
      RecordSuccessfullyInserted := True;

      case CurrentRecordType is
         when DNS_Types.A => --A records
                             --next data item must be an ipv4 addr
            Zone_File_Parser.ParseIPV4 (CurrentIPV4,
                                        CurrentLine,
                                        LastPos,
                                        Success);

            --can now build and insert a complete A record
            if Success then
               DNS_Table_Pkg.DNS_Table.InsertARecord
                 (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                  RR_Type.A_Record_Type.ARecordType'
                    (TTLInSeconds => CurrentTTL,
                     Class        => CurrentClass,
                     IPV4         => CurrentIPV4),
                  RecordSuccessfullyInserted);
            end if;

         when DNS_Types.AAAA => --AAAA records
                                --next item must be an ipv6 address
            Zone_File_Parser.ParseIpv6
              (CurrentIPV6, CurrentLine, LastPos, Success);

            --can now build and insert a complete AAAA record
            if Success then
               DNS_Table_Pkg.DNS_Table.InsertAAAARecord
                 (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                  RR_Type.AAAA_Record_Type.AAAARecordType'
                    (TTLInSeconds => CurrentTTL,
                     Class        => CurrentClass,
                     IPV6         => CurrentIPV6),
                  RecordSuccessfullyInserted);
            end if;

         when DNS_Types.CName => --CName records
                                 --next item must be a domain name
            Zone_File_Parser.ParseDomainName
              (CurrentDomainName, CurrentLine, LastPos, Success);

            if Success then
               --if domain name does not end in '.', append value of $ORIGIN
               Parser_Utilities.CheckAndAppendOrigin
                 (CurrentDomainName,
                  CurrentOrigin,
                  CurrentLine,
                  LastPos,
                  LineCount,
                  Success);
            end if;

            --can now build and insert a complete CNAME record
            if Success then
               DNS_Table_Pkg.DNS_Table.InsertCNameRecord
                 (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                  RR_Type.CName_Record_Type.CNameRecordType'
                    (TTLInSeconds         => CurrentTTL,
                     Class                => CurrentClass,
                     CanonicalDomainName  =>
                       RR_Type.ConvertDomainNameToWire (CurrentDomainName)),
                  RecordSuccessfullyInserted);
            end if;

         when DNS_Types.MX => --MX records
                              --next must come a preference value, then a
                              --domain name (mail exchanger)
            Zone_File_Parser.ParsePrefAndDomainName
              (CurrentPref, CurrentDomainName, CurrentLine, LastPos, Success);
            if Success then
               --if domain name does not end in '.', append value of $ORIGIN
               Parser_Utilities.CheckAndAppendOrigin
                 (CurrentDomainName,
                  CurrentOrigin,
                  CurrentLine,
                  LastPos,
                  LineCount,
                  Success);
            end if;

            if Success then
               --can now build and insert a complete MX record
               DNS_Table_Pkg.DNS_Table.InsertMXRecord
                 (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                  RR_Type.MX_Record_Type.MXRecordType'
                    (TTLInSeconds  => CurrentTTL ,
                     Class         => CurrentClass,
                     Pref          => CurrentPref,
                     MailExchanger =>
                       RR_Type.ConvertDomainNameToWire (CurrentDomainName)),
                  RecordSuccessfullyInserted);
            end if;

         when DNS_Types.Srv => --Srv records
                               --next must come preference value, weight, port,
                               --then a domain name (server name)
            Zone_File_Parser.ParsePrefWeightPortAndDomainName
              (CurrentPref,
               CurrentWeight,
               CurrentPort,
               CurrentDomainName,
               CurrentLine,
               LastPos,
               Success);
            if Success then
               --if domain name does not end in '.', append value of $ORIGIN
               Parser_Utilities.CheckAndAppendOrigin
                 (CurrentDomainName,
                  CurrentOrigin,
                  CurrentLine,
                  LastPos,
                  LineCount,
                  Success);
            end if;

            if Success then
               --can now build and insert a complete SRV record
               DNS_Table_Pkg.DNS_Table.InsertSrvRecord
                 (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                  RR_Type.Srv_Record_Type.SrvRecordType'
                    (TTLInSeconds => CurrentTTL ,
                     Class        => CurrentClass,
                     Pref         => CurrentPref,
                     Weight       => CurrentWeight,
                     PortNum      => CurrentPort,
                     ServerName   =>
                       RR_Type.ConvertDomainNameToWire (CurrentDomainName)),
                  RecordSuccessfullyInserted);
            end if;

         WHEN DNS_Types.NS => --NS records
                              --next item must be a valid host name
            Zone_File_Parser.ParseDomainName
              (CurrentDomainName, CurrentLine, LastPos, Success);
            Parser_Utilities.CheckValidHostName (CurrentDomainName, Success);
            if Success then
               --if domain name does not end in '.', append value of $ORIGIN
               Parser_Utilities.CheckAndAppendOrigin
                 (CurrentDomainName,
                  CurrentOrigin,
                  CurrentLine,
                  LastPos,
                  LineCount,
                  Success);
            end if;

            if Success then
               --can now build and insert a complete NS record
               DNS_Table_Pkg.DNS_Table.InsertNSRecord
                 (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                  RR_Type.NS_Record_Type.NSRecordType'
                    (TTLInSeconds => CurrentTTL ,
                     Class        => CurrentClass,
                     NameServer   =>
                       RR_Type.ConvertDomainNameToWire (CurrentDomainName)),
                  RecordSuccessfullyInserted);
            end if;

         when DNS_Types.Ptr => --Ptr records
            Zone_File_Parser.ParseDomainName
              (CurrentDomainName, CurrentLine, LastPos, Success);
            if Success then
               --if domain name does not end in '.', append value of $ORIGIN
               Parser_Utilities.CheckAndAppendOrigin
                 (CurrentDomainName,
                  CurrentOrigin,
                  CurrentLine,
                  LastPos,
                  LineCount,
                  Success);
            end if;

            if Success then
               --can now build and insert a complete PTR record
               DNS_Table_Pkg.DNS_Table.InsertPTRRecord
                 (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                  RR_Type.Ptr_Record_Type.PtrRecordType'
                    (TTLInSeconds => CurrentTTL,
                     Class        => CurrentClass,
                     DomainName   =>
                       RR_Type.ConvertDomainNameToWire (CurrentDomainName)),
                  RecordSuccessfullyInserted);
            end if;

         when DNS_Types.SOA => --SOA records
            InMultilineRecord := True;
            LineInRecordCtr := 0;
            Zone_File_Parser.ParseNameServerAndEmail (CurrentNameServer,
                                                      CurrentEmail,
                                                      CurrentLine,
                                                      LastPos,
                                                      Success);
            --complete SOA record is inserted later, after all the other fields
            --parsed

            --if name server or email do not end in '.', append value of $ORIGIN
            if Success then
               Parser_Utilities.CheckAndAppendOrigin
                 (CurrentNameServer,
                  CurrentOrigin,
                  CurrentLine,
                  LastPos,
                  LineCount,
                  Success);
            end if;

            --if name server or email do not end in '.', append value of $ORIGIN
            if Success then
               Parser_Utilities.CheckAndAppendOrigin
                 (CurrentEmail,
                  CurrentOrigin,
                  CurrentLine,
                  LastPos,
                  LineCount,
                  Success);
            end if;

            Parser_Utilities.CheckValidHostName (CurrentNameServer, Success);
            --NOTE:  CurrentEmail should eventually be checked too, but under
            --slightly different rules, see pg 77 of 4th edition O'Reilly BIND
            --book

            --DNSSec records below
         when DNS_Types.DNSKey => --DNSKey records
            InMultilineRecord := True;
            LineInRecordCtr := 0;
            Zone_File_Parser.ParseDNSKeyHeader
              (DNSKey_Rec, CurrentLine, LastPos, Success);
            --complete DNSKey record will be inserted later, after key field parsed

         when DNS_Types.NSec =>
            Zone_File_Parser.ParseDomainNameAndRRString
              (CurrentDomainName, RRString, CurrentLine, LastPos, Success);
            Parser_Utilities.CheckValidHostName (CurrentDomainName, Success);
            if Success then
               --if domain name does not end in '.', append value of $ORIGIN
               Parser_Utilities.CheckAndAppendOrigin
                 (CurrentDomainName,
                  CurrentOrigin,
                  CurrentLine,
                  LastPos,
                  LineCount,
                  Success);
            end if;
            Zone_File_Parser.FillBlockInfo
              (RRString,
               NumberOfRecordTypes,
               RecordTypes,
               NumberOfBlocks,
               BlockNumbers,
               BlockLengths,
               BitMaps,
               LineCount,
               Success);
            if Success then
               --can now build and insert a complete NSEC record
               DNS_Table_Pkg.DNS_Table.InsertNSecRecord
                 (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                  RR_Type.NSec_Record_Type.NSecRecordType'
                    (TTLInSeconds        => CurrentTTL,
                     Class               => CurrentClass,
                     RecordList          => RRString,
                     NumberOfRecordTypes => NumberOfRecordTypes,
                     RecordTypes         => RecordTypes,
                     NumberOfBlocks      => NumberofBlocks,
                     BlockNumbers        => BlockNumbers,
                     BlockLengths        => BlockLengths,
                     BitMaps             => BitMaps,
                     NextDomainName      =>
                       RR_Type.ConvertDomainNameToWire (CurrentDomainName)),
                  RecordSuccessfullyInserted);
            else  --must have been missing a record type
               Error_Msgs.PrintMissingRecordTypeErrorInfo (CurrentLine,
                                                           LastPos,
                                                           LineCount);
            end if;

         when DNS_Types.RRSig =>
            InMultilineRecord := True;
            LineInRecordCtr := 0;
            Zone_File_Parser.ParseRRSigHeader (RRSIG_Rec,
                                               CurrentLine,
                                               LastPos,
                                               Success);

         when others => -- can add more supported types here if needed
            Error_Msgs.PrintUnsupportedRecordWarning (CurrentLine,
                                                      LastPos,
                                                      LineCount);
      end case;
   end ProcessFirstLineOfRecord;
end Process_First_Line_Of_Record;
