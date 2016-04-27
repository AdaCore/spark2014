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

with Ada.Text_IO, Ada.Integer_Text_IO,
     RR_Type.DNSKey_Record_Type,
     RR_Type.NSEC_Record_Type;

package body Error_Msgs
  with SPARK_Mode => Off
is
   package M_IO is new Ada.Text_IO.Modular_IO (Unsigned_Types.Unsigned32);

   procedure PrintUnsupportedRecordWarning
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount  : in Unsigned_Types.Unsigned32)
   is
   begin
      Ada.Text_Io.Put ("Warning:  Unsupported record type at line # ");
      M_IO.Put (Item => LineCount, Width => 1);
      Ada.Text_IO.Put (" in zone file: ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put("    ");
      Ada.Text_IO.Put(CurrentLine (1 .. Length));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("Record ignored ");
      Ada.Text_IO.New_Line;
   end PrintUnsupportedRecordWarning;

   procedure PrintZeroTTLWarning
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   is
   begin
      Ada.Text_IO.Put ("Warning:  Default TTL of zero implied at line # ");
      M_IO.Put (Item => LineCount, Width => 1);
      Ada.Text_IO.Put (" in zone file: ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("    ");
      Ada.Text_IO.Put (CurrentLine (1 .. Length));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("Possible missing $TTL control statement ");
      Ada.Text_IO.New_Line;
   end PrintZeroTTLWarning;

   procedure PrintBlankOriginWarning
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32) is
   begin
      Ada.Text_IO.Put ("Warning:  Default blank ORIGIN appended");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("to domain name at line # ");
      M_IO.Put (Item => LineCount, Width => 1);
      Ada.Text_IO.Put (" in zone file: ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("    ");
      Ada.Text_IO.Put (CurrentLine (1 .. Length));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put("Possible missing $ORIGIN control statement ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("or missing period at end of domain name ");
      Ada.Text_IO.New_Line;
   end PrintBlankOriginWarning;

   procedure PrintTooManyRecordTypesInNSecRecordWarning
     (LineCount : in Unsigned_Types.Unsigned32)
   is
   begin
      Ada.Text_Io.Put
        ("Warning:  Maximum supported number of record types exceeded ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("in NSEC record at line # ");
      M_IO.Put (Item => LineCount, Width => 1);
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("Maximum number is ");
      Ada.Text_IO.Put
        (Item => Integer'Image
                   (RR_Type.NSec_Record_Type.MaxNumberOfRecordTypes));
      Ada.Text_IO.Put (".  Further record types ignored.");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put
        ("To process the entire NSEC record, source code must be recompiled ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put
        ("with larger value of rr_type.nsec_record_type.maxNumberOfRecordTypes"
         & "and revalidated.");
      Ada.Text_IO.New_Line;
   end PrintTooManyRecordTypesInNSecRecordWarning;

   procedure PrintParseErrorInfo
     (currentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   is
   begin
      Ada.Text_Io.Put("Invalid or unsupported record on line # ");
      M_IO.Put (Item => LineCount, Width => 1);
      Ada.Text_IO.Put (" in zone file: ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("    ");
      Ada.Text_IO.Put (CurrentLine (1 .. Length));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("Remaining lines in zone file ignored.");
      Ada.Text_IO.New_Line;
   end PrintParseErrorInfo;

   procedure PrintMissingRecordTypeErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   is
   begin
      Ada.Text_IO.Put ("Invalid NSEC record on line # ");
      M_IO.Put (Item => LineCount, Width => 1);
      Ada.Text_IO.Put (" of zone file: ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("    ");
      Ada.Text_IO.Put (CurrentLine (1 .. Length));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("NSEC record must contain at least one record type");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("Remaining lines in zone file ignored.");
      Ada.Text_IO.New_Line;
   end PrintMissingRecordTypeErrorInfo;

   procedure PrintSOARecordErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32) is
   begin
      Ada.Text_IO.Put ("Disallowed SOA record on line # ");
      M_IO.Put (Item => LineCount, Width => 1);
      Ada.Text_IO.Put (" of zone file: ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("    ");
      Ada.Text_IO.Put (CurrentLine (1 .. Length));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put
        ("Only one SOA record is permitted in a zone file (RFC 1035)");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("Remaining lines in zone file ignored.");
      Ada.Text_IO.New_Line;
   end PrintSOARecordErrorInfo;

   procedure PrintAppendDomainLengthErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   is
   begin
      Ada.Text_IO.Put
        ("ERROR IN ZONE FILE on line # " &
         Unsigned_Types.Unsigned32'Image (LineCount));
      Ada.Text_IO.Put (" of zone file:");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("    ");
      Ada.Text_IO.Put (CurrentLine (1 .. Length));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_line;
      Ada.Text_IO.Put ("domain name after appending with $ORIGIN is too long ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("(maximum length is ");
      Ada.Integer_Text_IO.Put (Item  => RR_Type.MaxDomainNameLength - 1,
                               Width => 1);
      Ada.Text_IO.Put (" chars)");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("Domain name must either be changed, or source code " &
                       "recompiled ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("(with larger value of rr_type.MaxDomainNameLength) " &
                       "and revalidated.");
      Ada.Text_IO.New_Line;
      Ada.text_io.Put ("Remaining lines in zone file ignored.");
      Ada.Text_IO.New_Line;
   end PrintAppendDomainLengthErrorInfo;

   procedure PrintLineLengthErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   is
   begin
      Ada.Text_IO.Put ("ERROR:  Line #");
      M_IO.Put (Item => LineCount, Width => 1);
      Ada.Text_IO.Put (" in zone file is too long (");
      Ada.Integer_Text_IO.Put (Item => Length, Width => 1);
      Ada.Text_IO.Put (" chars, maximum length is ");
      Ada.Integer_Text_IO.Put (Item => RR_Type.MaxLineLength-1, Width => 1);
      Ada.Text_IO.Put (")");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("    ");
      Ada.Text_IO.Put (CurrentLine (1 .. Length));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put
        ("Line must either be broken up, or source code recompiled ");
      Ada.Text_IO.Put
        ("(with larger value of rr_type.MaxLineLength) and revalidated.");
      Ada.Text_IO.New_Line;
      Ada.text_io.Put ("Remaining lines in zone file ignored.");
      Ada.Text_IO.New_Line;
   end PrintLineLengthErrorInfo;

   procedure PrintDomainLengthErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      BegIdx      : in Natural;
      EndIdx      : in Natural)
   is
   begin
      Ada.Text_IO.Put ("ERROR IN ZONE FILE: domain name is too long (");
      Ada.Integer_Text_IO.Put (Item => EndIdx - BegIdx + 1, Width => 1);
      Ada.Text_IO.Put (" chars, maximum length is ");
      Ada.Integer_Text_IO.Put
        (Item => RR_Type.MaxDomainNameLength-1, Width => 1);
      Ada.Text_IO.Put(")");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put("    ");
      Ada.Text_IO.Put(currentLine(begIdx..endIdx));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put
        ("Domain name must either be changed, or source code recompiled ");
      Ada.Text_IO.Put
        ("(with larger value of rr_type.MaxDomainNameLength) and revalidated.");
      Ada.Text_IO.New_Line;
      Ada.text_IO.Put ("Remaining lines in zone file ignored.");
      Ada.Text_IO.New_Line;
   end PrintDomainLengthErrorInfo;

   procedure PrintRRStringLengthErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      BegIdx      : in Natural;
      EndIdx      : in Natural)
   is
   begin
      Ada.Text_IO.Put
        ("ERROR IN ZONE FILE: resource record string is too long (");
      Ada.Integer_Text_IO.Put (Item => EndIdx - BegIdx + 1, Width => 1);
      Ada.Text_IO.Put (" chars, maximum length is ");
      Ada.Integer_Text_IO.Put
        (Item => RR_Type.MaxDomainNameLength - 1, Width => 1);
      Ada.Text_IO.Put(")");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("    ");
      Ada.Text_IO.Put (CurrentLine (BegIdx .. EndIdx));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put
        ("Either NSEC record must be changed, or source code recompiled ");
      Ada.Text_IO.Put
        ("(with redefinition of rr_type.nsec_record_type.recordListType) "&
         "and revalidated.");
      Ada.Text_IO.New_Line;
      Ada.text_io.Put ("Remaining lines in zone file ignored.");
      Ada.Text_IO.New_Line;
   end PrintRRStringLengthErrorInfo;

   procedure PrintKeyLengthErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in unsigned_types.Unsigned32)
   is
   begin
      Ada.Text_IO.Put ("ERROR:  Key fragment at line #");
      M_IO.Put (Item => LineCount, Width => 1);
      Ada.Text_IO.Put
        (" in zone file makes key too long (maximum length is ");
      Ada.Integer_Text_IO.Put
        (Item => RR_Type.DNSKey_Record_Type.MaxDNSKeyLength, Width => 1);
      Ada.Text_IO.Put (")");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("    ");
      Ada.Text_IO.Put (CurrentLine (1 .. Length));
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("Server source code must be recompiled ");
      Ada.Text_IO.Put
        ("(with larger value of Rr_Type.dnskey_record_type.maxDNSKeyLength " &
         "or ");
      Ada.Text_IO.New_Line;
      ada.Text_IO.Put
        ("Rr_Type.dnskey_record_type.maxRRSIGLength as appropriate) and " &
         "revalidated.");
      Ada.Text_IO.New_Line;
      Ada.text_io.Put ("Remaining lines in zone file ignored.");
      Ada.Text_IO.New_Line;
   end PrintKeyLengthErrorInfo;


   procedure PrintDNSTableFullInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      LineCount   : in Unsigned_Types.Unsigned32)
   is
   begin
      Ada.Text_IO.Put ("ERROR:  Zone file contains too many records,");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("or more than one SOA record for a given domain.");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("There is no room for the record at line # ");
      M_IO.Put (Item => LineCount, Width => 1);
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("    ");
      Ada.Text_IO.Put(currentLine);
      Ada.Text_IO.New_Line;
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put
        ("If the problem is due to multiple SOA records for a given domain,");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put
        ("you will need to remove the extra SOA records from the zone file.");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put
        ("Otherwise, shut down and rebuild the server, with source code " &
         "recompiled ");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put
        ("(use larger value(s) of rr_type.MaxNumRecords and/or " &
         "rr_type.NumBuckets) and revalidated.");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("Remaining lines in zone file ignored.");
      Ada.Text_IO.New_Line;
   end PrintDNSTableFullInfo;

   --should only be called in conjunction with file reading "Success" variable
   --set to false
   procedure PrintMissingSOARecordInfo is
   begin
      Ada.Text_IO.Put
        ("ERROR:  First record in zone file must be an SOA record.");
      Ada.Text_IO.New_Line;
      Ada.Text_IO.Put ("Remaining lines in zone file ignored.");
      Ada.Text_IO.New_Line;
   end PrintMissingSOARecordInfo;

end Error_Msgs;
