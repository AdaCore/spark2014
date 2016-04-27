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
     RR_Type.DNSKey_Record_Type,
     RR_Type.RRSig_Record_Type,
     Unsigned_Types,
     RR_Type,
     Spark.Text_IO;

use type RR_Type.RRItemType,
         DNS_Types.Query_Type,
         Unsigned_Types.Unsigned32;

package Process_First_Line_Of_Record is
   procedure ProcessFirstLineOfRecord
     (CurrentRecordType          : in     DNS_Types.Query_Type;

      --common to all record types
      CurrentOrigin              : in     RR_Type.DomainNameStringType;
      CurrentOwner               : in     RR_Type.DomainNameStringType;
      CurrentTTL                 : in     Unsigned_Types.Unsigned32;
      CurrentClass               : in     RR_Type.ClassType;
      CurrentLine                : in     RR_Type.LineFromFileType;
      Lastpos                    : in     RR_Type.Linelengthindex;
      LineCount                  : in     Unsigned_Types.Unsigned32;
      --for multiline records
      InMultilineRecord          :    out Boolean;
      LineInRecordCtr            :    out Unsigned_Types.Unsigned32;
      --SOA record fields
      CurrentNameServer          :    out RR_Type.DomainNameStringType;
      CurrentEmail               :    out RR_Type.DomainNameStringType;
      --DNSKey record (if needed)
      DNSKey_Rec                 :    out RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
      --RRSig record (if needed)
      RRSig_Rec                  :    out RR_Type.RRSig_Record_Type.RRSigRecordType;
      RecordSuccessfullyInserted :    out Boolean;
      Success                    : in out Boolean)
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => ((CurrentEmail,
                     CurrentNameServer,
                     Success) => (CurrentLine,
                                  CurrentOrigin,
                                  CurrentRecordType,
                                  LastPos,
                                  Success),
                    (DNSKey_Rec,
                     RRSig_Rec) => (CurrentLine,
                                    CurrentRecordType,
                                    LastPos,
                                    Success),
                    DNS_Table_Pkg.DNS_Table =>+ (CurrentClass,
                                                 CurrentLine,
                                                 CurrentOrigin,
                                                 CurrentOwner,
                                                 CurrentRecordType,
                                                 CurrentTTL,
                                                 LastPos,
                                                 Success),
                    (InMultilineRecord,
                     LineInRecordCtr) => CurrentRecordType,
                    RecordSuccessfullyInserted => (CurrentLine,
                                                   CurrentOrigin,
                                                   CurrentOwner,
                                                   CurrentRecordType,
                                                   DNS_table_pkg.DNS_Table,
                                                   LastPos,
                                                   Success),
                    null => LineCount),
        Pre     => LastPos >= 1 and LastPos <= RR_Type.LineLengthIndex'Last;
end Process_First_Line_Of_Record;
