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
     DNS_Table_Pkg,
     Parser_Utilities,
     Process_First_Line_Of_Record,
     Zone_File_Parser,
     Error_Msgs,
     Unsigned_Types,
     RR_Type;

with RR_Type.DNSKey_Record_Type,
     RR_Type.RRSig_Record_Type,
     RR_Type.SOA_Record_Type;

with Spark.Text_IO;

use type RR_Type.RRItemType,
         DNS_Types.Query_Type,
         Unsigned_Types.Unsigned32;

--just in case debugging needed

--WITH Ada.Text_IO, Ada.Integer_Text_IO;


package body Zone_File_Io is

   procedure ProcessZoneFile
     (ZoneFile : in out Spark.Text_IO.File_Type;
      Success  :    out Boolean)
   is
      CurrentLine : RR_Type.LineFromFileType :=
        RR_Type.LineFromFileType'(others => ' ');
      LastPos : Natural := 0;
      LineTooLong : Boolean;
      KeyTooLong : Boolean := False;
      BlankLine : Boolean;
      CommentLine : Boolean := False; --True if line is a comment
      ControlLine : Boolean := False; --True if line is a control
                                      --statement (e.g. $TTL)
      HaveSOARecord : Boolean := False; --set to True if first record is SOA
      Parseable : Boolean;
      AllDone : Boolean;
      ReturnedType : RR_Type.RRItemType := RR_Type.Other;
      RecordSuccessfullyInserted : Boolean := True;
      LineCount : Unsigned_Types.Unsigned32 := 0;  --will wrap around if file
                                                   --has 2^32 lines :-)
      RRCtr : Unsigned_Types.Unsigned32 := 0;  --counts resource recs, see above
      InMultilineRecord : Boolean := False;
      LineInRecordCtr : Unsigned_Types.Unsigned32 := 0; --first line of
                                                        --multiline record is 0
      BegIdx : RR_Type.LineLengthIndex;
      EndIdx : RR_Type.LineLengthIndex;

      CurrentOrigin : RR_Type.DomainNameStringType := RR_Type.BlankDomainName;
      CurrentOwner : RR_Type.DomainNameStringType := RR_Type.BlankDomainName;
      CurrentTTL : Unsigned_Types.Unsigned32 := 0;
      CurrentClass : RR_Type.ClassType := RR_Type.Internet;

      CurrentRecordType : DNS_Types.Query_Type := DNS_Types.A;

      --SOA record fields
      CurrentNameServer : RR_Type.DomainNameStringType :=
        RR_Type.BlankDomainName;

      --if we need a DNSKey record
      DNSKey_Rec : RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
      --if we need an RRSig record
      RRSig_Rec : RR_Type.RRSig_Record_Type.RRSigRecordType;

      --(these initial values never used, but make flow errors go away)
      CurrentEmail : RR_Type.DomainNameStringType := RR_Type.BlankDomainName;
      CurrentSerialNumber : Unsigned_Types.Unsigned32 := 0;
      CurrentRefresh : Unsigned_Types.Unsigned32 := 0;
      CurrentRetry : Unsigned_Types.Unsigned32 := 0;
      CurrentExpiry : Unsigned_Types.Unsigned32 := 0;
      CurrentMinimum : Unsigned_Types.Unsigned32 := 0;

      -- Used to test the last section of an Srv record
      -- testOwner: RR_Type.DomainNameStringType := RR_Type.BlankDomainName;

   begin
      --make bogus flow errors go away
      DNSKey_Rec := RR_Type.DNSKey_Record_Type.BlankDNSKeyRecord;
      RRSig_Rec := RR_Type.RRSig_Record_Type.BlankRRSigRecord;
      Success := True;

      --grab first line if file opened OK
      Spark.Text_IO.Get_Line
        (File => ZoneFile,
         Item => CurrentLine,
         Last => LastPos);
      LineCount := LineCount + 1;

      while Success loop
         BlankLine := LastPos = 0;
         LineTooLong := LastPos >= RR_Type.MaxLineLength;
         if LineTooLong then
            Error_Msgs.PrintLineLengthErrorInfo
              (CurrentLine,
               LastPos,
               LineCount);
            Success := False;
         elsif not BlankLine then
            Parser_Utilities.FindFirstToken
              (CurrentLine,
               LastPos,
               ReturnedType);
            CommentLine := ReturnedType = RR_Type.Comment;
            ControlLine := ReturnedType = RR_Type.Control;
         end if;

         Parseable := not BlankLine and
                      not LineTooLong and
                      not CommentLine;
         if Parseable then
            if not InMultilineRecord then
            --multiline records treated differently

               --for monoline records, build record from line and insert in
               --appropriate table
               if ControlLine then
                  --control statements are monoline, but different from DNS
                  --records
                  Zone_File_Parser.ParseControlLine
                    (CurrentOrigin,
                     CurrentTTL,
                     CurrentLine,
                     LastPos,
                     Success);
               else
                  --if not a control line, grab the owner, TTL, class and
                  --record type
                  RRCtr := RRCtr + 1;

                  Zone_File_Parser.ParseOwnerTTLClassAndRecordType
                    (CurrentOwner,
                     CurrentTTL,
                     CurrentClass,
                     CurrentRecordType,
                     CurrentLine,
                     LastPos,
                     Success);

                  if Success then
                     if CurrentTTL = 0 then
                        Error_Msgs.PrintZeroTTLWarning
                          (CurrentLine,
                           LastPos,
                           LineCount);
                     end if;
                     --if domain name does not end in '.', append value of
                     --$ORIGIN
                     Parser_Utilities.CheckAndAppendOrigin
                       (CurrentOwner,
                        CurrentOrigin,
                        CurrentLine,
                        LastPos,
                        LineCount,
                        Success);

                     --owners for A, AAAA, DNSKEY, or MX records must be valid
                     --host names, check those more carefully
                     if CurrentRecordType = DNS_Types.A or
                       CurrentRecordType = DNS_Types.AAAA or
                       CurrentRecordType = DNS_Types.DNSKey or
                       CurrentRecordType = DNS_Types.MX
                     then
                        Parser_Utilities.CheckValidHostName
                          (CurrentOwner, Success);
                     elsif CurrentRecordType = DNS_Types.Srv then
                        Parser_Utilities.CheckValidSRVOwner
                          (CurrentOwner, Success);
                     end if;

                     if Success then
                        --handle the record and (if not multiline) put it in
                        --the DNS table
                        Process_First_Line_Of_Record.ProcessFirstLineOfRecord
                          (CurrentRecordType,
                           CurrentOrigin,
                           CurrentOwner,
                           CurrentTTL,
                           CurrentClass,
                           CurrentLine,
                           LastPos,
                           LineCount,
                           InMultilineRecord,
                           LineInRecordCtr,
                           CurrentNameServer,
                           CurrentEmail,
                           DNSKey_Rec,
                           RRSig_Rec,
                           RecordSuccessfullyInserted,
                           Success);
                     end if;
                  end if;   --successful parse of owner/ttl/class/recordType
               end if;  --control line or other monoline record
            else  --inside a multiline record
               case CurrentRecordType is
                  when DNS_Types.SOA =>
                     --parsing the numeric fields of an SOA record ( after the
                     --'(' )

                     --must be one per line
                     LineInRecordCtr := LineInRecordCtr + 1;
                     case lineInRecordCtr is
                        when 1 =>
                           Zone_File_Parser.ParseSerialNumber
                             (CurrentSerialNumber,
                              CurrentLine,
                              LastPos,
                              Success);
                        when 2 =>
                           Zone_File_Parser.ParseTimeSpec
                             (CurrentRefresh,
                              CurrentLine,
                              LastPos,
                              Success);
                        when 3 =>
                           Zone_File_Parser.ParseTimeSpec
                             (CurrentRetry, CurrentLine, LastPos, Success);
                        when 4 =>
                           Zone_File_Parser.ParseTimeSpec
                             (CurrentExpiry, CurrentLine, LastPos, Success);
                        when 5 =>
                           Zone_File_Parser.ParseTimeSpec
                             (CurrentMinimum, CurrentLine, LastPos, Success);
                           --check if the token after the time specifier is a
                           --right paren
                           BegIdx := 1;
                           Parser_Utilities.FindNextToken
                             (CurrentLine,
                              LastPos,
                              BegIdx,
                              EndIdx,
                              ReturnedType);
                           --BegIdx <= EndIdx always true,
                           --makes flow errors go away
                           if ReturnedType = RR_Type.DomainNameOrTimeSpec and
                             BegIdx <= EndIdx and
                             EndIdx < LastPos
                           then
                     	        BegIdx := EndIdx + 1;
                           end if;
                           Parser_Utilities.FindNextToken
                             (CurrentLine,
                              LastPos,
                              BegIdx,
                              EndIdx,
                              ReturnedType);
                           --BegIdx <= EndIdx always true,
                           --makes flow errors go away
                           if ReturnedType = RR_Type.RParen and
                             BegIdx <= EndIdx
                           then
                              InMultilineRecord := False;
                              DNS_Table_Pkg.DNS_Table.InsertSOARecord
                                (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                                 RR_Type.SOA_Record_Type.SOARecordType'
                                   (TTLInSeconds => CurrentTTL,
                                    Class        => CurrentClass,
                                    NameServer   =>
                                      RR_Type.ConvertDomainNameToWire
                                        (CurrentNameServer),
                                    Email        =>
                                      RR_Type.ConvertDomainNameToWire
                                        (CurrentEmail),
                                    SerialNumber => CurrentSerialNumber,
                                    Refresh      => CurrentRefresh,
                                    Retry        => CurrentRetry,
                                    Expiry       => CurrentExpiry,
                                    Minimum      => CurrentMinimum),
                                 RecordSuccessfullyInserted);
                              HaveSOARecord := HaveSOARecord or
                                (RecordSuccessfullyInserted and RRCtr = 1);
                           end if;

                        when others =>
                           if ReturnedType = RR_Type.RParen then
                              InMultilineRecord := False;
                              DNS_Table_Pkg.DNS_Table.InsertSOARecord
                                (RR_Type.ConvertDomainNameToWire(CurrentOwner),
                                 RR_Type.SOA_Record_Type.SOARecordType'
                                   (TTLInSeconds => CurrentTTL,
                                    Class        => CurrentClass,
                                    NameServer   =>
                                      RR_Type.ConvertDomainNameToWire
                                        (CurrentNameServer),
                                    Email        =>
                                      RR_Type.ConvertDomainNameToWire
                                        (CurrentEmail),
                                    SerialNumber => CurrentSerialNumber,
                                    Refresh      => CurrentRefresh,
                                    Retry        => CurrentRetry,
                                    Expiry       => CurrentExpiry,
                                    Minimum      => CurrentMinimum),
                                 RecordSuccessfullyInserted);
                              HaveSOARecord := HaveSOARecord or
                                (RecordSuccessfullyInserted and RRCtr = 1);
                           else
                              Success := False;
                           end if;
                     end case; --LineInRecordCtr value
                  when DNS_Types.DNSKey =>
                     --parsing the lines of a DNSKey record ( after the '(' )
                     --each line is a piece of the key, except for the last
                     LineInRecordCtr := LineInRecordCtr + 1;
                     --check if line begins with ')'
                     BegIdx := 1;
                     Parser_Utilities.FindNextToken
                       (CurrentLine, LastPos, BegIdx, EndIdx, ReturnedType);
                     --if ')' found, record complete, can insert in table
                     --BegIdx <= EndIdx always true, makes flow errors go away
                     if ReturnedType = RR_Type.RParen and BegIdx <= EndIdx then
                        InMultilineRecord := False;
                        DNSKey_Rec.TTLInSeconds := CurrentTTL;
                        DNSKey_Rec.Class := CurrentClass;
                        --flags, protocol, algorithm already set when first
                        --line processed, key and keyLength set when
                        --remaining lines processed, so we're done
                        DNS_Table_Pkg.DNS_Table.InsertDNSKeyRecord
                          (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                           DNSKey_Rec,
                           RecordSuccessfullyInserted);
                     else
                        --otherwise we're still in the middle of a DNSKey
                        --record, parsing the key
                        Parser_Utilities.AddToKey
                          (DNSKey_Rec, CurrentLine, LastPos, Success);
                        if not Success then
                           KeyTooLong := True;
                        end if;
                     end if;
                  when DNS_Types.RRSig =>
                     --parsing the lines of an RRSIG record after the first one
                     --2nd line has record fields, the rest of the lines are
                     --the key terminated by a right paren
                     LineInRecordCtr := LineInRecordCtr + 1;
                     case LineInRecordCtr is
                        when 1 =>
                           Zone_File_Parser.ParseRRSig2ndLine
                             (RRSig_Rec, CurrentLine, LastPos, Success);
                        when others =>
                           Parser_Utilities.AddToKeyR
                             (RRSig_Rec,
                              CurrentLine,
                              LastPos,
                              AllDone,
                              Success);
                           if not Success then
                              KeyTooLong := True;
                           elsif AllDone then
                              RRSig_Rec.TTLInSeconds := CurrentTTL;
                              RRSig_Rec.Class := CurrentClass;
                              DNS_Table_Pkg.DNS_Table.InsertRRSigRecord
                                (RR_Type.ConvertDomainNameToWire (CurrentOwner),
                                 RRSig_Rec,
                                 RecordSuccessfullyInserted);
                              InMultilineRecord := False;
                           end if;
                     end case;

                  when others => --other multiline record types can go here
                     null;
               end case; --multiline record types
            end if; --parsing a multiline record
         else
            null;  --non-parseable line, blank lines/comments ignored
         end if;

         --check for various error conditions
         Success := Success and RecordSuccessfullyInserted;
         if not RecordSuccessfullyInserted then
            Error_Msgs.PrintDNSTableFullInfo (CurrentLine, LineCount);
         elsif KeyTooLong then
            Error_Msgs.PrintKeyLengthErrorInfo
              (CurrentLine, LastPos, LineCount);
         elsif not Success and not LineTooLong then
            Error_Msgs.PrintParseErrorInfo (CurrentLine, LastPos, LineCount);
         elsif not HaveSOARecord and RRCtr > 1 then
            Success := False;
            Error_Msgs.PrintMissingSOARecordInfo;
         elsif not LineTooLong then
            --looks like we're good, get the next line and repeat
            Spark.Text_IO.Get_Line
              (File => ZoneFile,
               Item => CurrentLine,
               Last => LastPos);
            --having old characters reset to blank helps with error reporting
            if LastPos >= 1 and LastPos < RR_Type.MaxLineLength then
               for I in Integer range LastPos + 1 .. RR_Type.MaxLineLength loop
                  CurrentLine(I) := ' ';
               end loop;
            end if;
            LineCount := LineCount + 1;
         end if;
      end loop; --file reading loop, one line per iteration

   end ProcessZoneFile;

end Zone_File_IO;
