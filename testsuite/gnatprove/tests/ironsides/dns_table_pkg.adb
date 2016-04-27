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

with Ada.Characters.Handling;

--In case debugging IO needed
--with Ada.Text_IO;

package body DNS_Table_Pkg is

   protected body DNS_Table_Type is
      --UTILITIES
      function To_Lower
        (DomainName : in RR_Type.WireStringType)
         return RR_Type.WireStringType
      is
         LowerCaseVersion : RR_Type.WireStringType := RR_Type.BlankWire;
         Length           : RR_Type.WireStringTypeIndex;
      begin
         Length := RR_Type.WireNameLength (DomainName);
         for I in Integer range 1 .. Length loop
            LowerCaseVersion (I) :=
              Ada.Characters.Handling.To_Lower (DomainName (I));
         end loop;
         return LowerCaseVersion;
      end To_Lower;

      function Same (X, Y : in RR_Type.WireStringType) return Boolean is
         (for all I in 1 .. RR_Type.WireNameLength (X) => X (I) = Y (I));

      function Hash
        (DomainName : in RR_Type.WireStringType)
         return RR_Type.NumBucketsIndexType
         --return val => (1 <= val and val <= RR_Type.NumBuckets);
      is
         NumCharsInHashFunction : constant Natural := 4;
         Val                    : Natural := 0;
      begin
         for I in Integer range 1 .. NumCharsInHashFunction loop
            pragma Loop_Invariant
              (Val <= (I - 1)*Character'Pos (Character'Last) and
               (for all Q in RR_Type.WireStringTypeIndex =>
                  Character'Pos (DomainName (Q)) <= 255 and
                  Character'Pos (DomainName (Q)) >= 0));
            Val := Val + Character'Pos (DomainName (I));
         end loop;
         return (Val mod RR_Type.NumBuckets) + 1;
      end Hash;

      --QUERY PROCEDURES
      procedure QueryARecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.A_Record_Type.ARecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         -- must initialize the whole array to make flow error go away
         -- ReturnedRecords := RR_Type.A_Record_Type.ARecordBucketType'(
         --   others => RR_Type.A_Record_Type.BlankARecord);
         Lower_DomainName := To_Lower (DomainName);

         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);
         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when ARecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            if Same (ARecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := ARecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QueryARecords;

      --QUERY PROCEDURES
      procedure CountARecords
        (DomainName : in     RR_Type.WireStringType;
         HowMany    :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         -- must initialize the whole array to make flow error go away
         Lower_DomainName := To_Lower (DomainName);

         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (DomainName);
         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when ARecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            --if To_Lower (ARecordTable(Bucket)(Ctr).Owner) =
            --     Lower_DomainName
            --then
            if Same (ARecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
            end if;
         end loop;
      end CountARecords;

      procedure CountAAAARecords
        (DomainName : in     RR_Type.WireStringType;
         HowMany    :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         -- must initialize the whole array to make flow error go away
         Lower_DomainName := To_Lower (DomainName);

         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (DomainName);
         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when AAAARecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            --if To_Lower(ARecordTable(Bucket)(Ctr).Owner) =
            --     Lower_DomainName
            --then
            if Same (AAAARecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany+1;
            end if;
         end loop;
      end CountAAAARecords;

      procedure QueryAAAARecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.AAAA_Record_Type.AAAARecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         Lower_DomainName := To_Lower (DomainName);
         -- must initialize the whole array to make flow error go away
         -- returnedRecords := RR_Type.aaaa_record_type.AAAARecordBucketType'(
         --   others => RR_Type.aaaa_record_type.blankAAAARecord);

         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);
         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when AAAARecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            --if To_Lower(AAAARecordTable(Bucket)(Ctr).Owner) =
            --     Lower_DomainName
            --then
            if Same (AaaaRecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := AAAARecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QueryAAAARecords;

      procedure QueryCNameRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.CName_Record_Type.CNameRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         Lower_DomainName := To_Lower (DomainName);
         -- must initialize the whole array to make flow error go away
         -- returnedRecords := RR_Type.CName_Record_Type.CNameRecordBucketType'(
         --   others => RR_Type.CName_Record_Type.BlankCNameRecord);

         -- queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);
         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when CNameRecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            if Same (CNameRecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := CNameRecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QueryCNameRecords;

      procedure QueryDNSKeyRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.DNSKey_Record_Type.DNSKeyRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         Lower_DomainName := To_Lower (DomainName);
         -- must initialize the whole array to make flow error go away
         -- returnedRecords := RR_Type.DNSKey_Record_Type.DNSKeyRecordBucketType'(
         --   others => RR_Type.DNSKey_Record_Type.BlankDNSKeyRecord);

         -- queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);
         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when DNSKeyRecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            if Same (DNSKeyRecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := DNSKeyRecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QueryDNSKeyRecords;

      procedure QueryMXRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.MX_Record_Type.MXRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         Lower_DomainName := To_Lower (DomainName);
         -- must initialize the whole array to make flow error go away
         -- returnedRecords := RR_Type.MX_Record_Type.MXRecordBucketType'(
         --   others => RR_Type.MX_Record_Type.BlankMXRecord);
         -- queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);

         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when MXRecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            if Same (MXRecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := MXRecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QueryMXRecords;

      procedure QuerySrvRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.Srv_Record_Type.SrvRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         Lower_DomainName := To_Lower (DomainName);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);

         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when SrvRecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            if Same (SrvRecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := SrvRecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QuerySrvRecords;

      procedure QueryNSRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.ns_record_type.NSRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         Lower_DomainName := To_Lower (DomainName);
         -- must initialize the whole array to make flow error go away
         -- returnedRecords := RR_Type.NS_Record_Type.NSRecordBucketType'(
         --   others => RR_Type.NS_Record_Type.BlankNSRecord);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);

         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when NSRecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            if Same (NSRecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := NSRecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QueryNSRecords;

      procedure QueryNSecRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.NSec_Record_Type.NSecRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         Lower_DomainName := To_Lower (DomainName);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);
         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when NSecRecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            if Same (NSecRecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := NSecRecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QueryNSecRecords;

      procedure QueryPtrRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.Ptr_Record_Type.PtrRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         Lower_DomainName := To_Lower (DomainName);
         -- must initialize the whole array to make flow error go away
         -- ReturnedRecords := RR_Type.Ptr_Record_Type.PtrRecordBucketType'(
         --   others => RR_Type.Ptr_Record_Type.BlankPtrRecord);
         -- queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);

         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when PtrRecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            if Same (PtrRecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := PtrRecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QueryPtrRecords;

      procedure QueryRRSIGRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.RRSig_Record_Type.RRSigRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         Lower_DomainName := To_Lower (DomainName);
         -- must initialize the whole array to make flow error go away
         -- ReturnedRecords := RR_Type.RRSig_Record_Type.RRSigRecordBucketType'(
         --   others => RR_Type.RRSig_Record_Type.BlankRRSigRecord);
         -- queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);
         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when RRSigRecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            if Same (RRSigRecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := RRSigRecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QueryRRSigRecords;

      procedure QuerySOARecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.SOA_Record_Type.SOARecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      is
         Bucket           : RR_Type.NumBucketsIndexType;
         Lower_DomainName : RR_Type.WireStringType;
      begin
         Lower_DomainName := To_Lower(DomainName);
         -- must initialize the whole array to make flow error go away
         -- ReturnedRecords := RR_Type.SOA_Record_Type.SOARecordBucketType'(
         --   others => RR_Type.SOA_Record_Type.BlankSOARecord);
         -- queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_DomainName);

         HowMany := 0;
         for Ctr in RR_Type.ReturnedRecordsIndexType loop
            pragma Loop_Invariant
              (HowMany >= 0 and
               HowMany < Ctr and
               Bucket >= 1 and
               Bucket <= RR_Type.NumBuckets);
            exit when SOARecordKeys (Bucket)(Ctr)(1) = ASCII.NUL;
            if Same (SOARecordKeys (Bucket)(Ctr), Lower_DomainName) then
               HowMany := HowMany + 1;
               ReturnedRecords (HowMany) := SOARecordTable (Bucket)(Ctr);
            end if;
         end loop;
      end QuerySOARecords;

      --INSERT PROCEDURES
      procedure InsertARecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.A_Record_Type.ARecordType;
         Success   :    out Boolean)
      is
         Bucket    : RR_Type.NumBucketsIndexType;
         Lower_Key : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower (Key);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_Key);

         Success := False;
         for I in RR_Type.ReturnedRecordsIndexType loop
            if ARecordKeys (Bucket)(I) = RR_Type.BlankOwner then
               ARecordKeys (Bucket)(I) := Lower_Key;
               ARecordTable (Bucket)(I) := TheRecord;
               Success := True;
            end if;
            exit when Success;
         end loop;
      end InsertARecord;

      procedure InsertAAAARecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.AAAA_Record_Type.AAAARecordType;
         Success   :    out Boolean)
      is
         Bucket    : RR_Type.NumBucketsIndexType;
         Lower_Key : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower(Key);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_Key);

         Success := False;
         for i in RR_Type.ReturnedRecordsIndexType loop
            if AAAARecordKeys (Bucket)(I) = RR_Type.BlankOwner then
               AAAARecordKeys (Bucket)(I) := Lower_Key;
               AAAARecordTable (Bucket)(I) := TheRecord;
               Success := True;
            end if;
            exit when Success;
         end loop;
      end InsertAAAARecord;

      procedure InsertCNameRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.CName_Record_Type.CNameRecordType;
         Success   :    out Boolean)
      is
         Bucket    : RR_Type.NumBucketsIndexType;
         Lower_Key : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower (Key);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_Key);

         Success := False;
         for I in RR_Type.ReturnedRecordsIndexType loop
            if CNameRecordKeys (Bucket)(I) = RR_Type.BlankOwner then
               CNameRecordKeys (Bucket)(I) := Lower_Key;
               CNameRecordTable (Bucket)(I) := TheRecord;
               Success := True;
            end if;
            exit when Success;
         end loop;
      end InsertCNameRecord;

      procedure InsertDNSKeyRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
         Success   :    out Boolean)
      is
         Bucket    : RR_Type.NumBucketsIndexType;
         Lower_Key : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower (Key);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_Key);

         Success := False;
         for I in RR_Type.ReturnedRecordsIndexType loop
            if DNSKeyRecordKeys (Bucket)(I) = RR_Type.BlankOwner then
               DNSKeyRecordKeys (Bucket)(I) := Lower_Key;
               DNSKeyRecordTable (Bucket)(I) := TheRecord;
               Success := True;
            end if;
            exit when Success;
         end loop;
      end InsertDNSKeyRecord;

      procedure InsertMXRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.MX_Record_Type.MXRecordType;
         Success   :    out Boolean)
      is
         Bucket    : RR_Type.NumBucketsIndexType;
         Lower_Key : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower (Key);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_Key);

         Success := False;
         for I in RR_Type.ReturnedRecordsIndexType loop
            if MXRecordKeys (Bucket)(I) = RR_Type.BlankOwner then
               MXRecordKeys (Bucket)(I) := Lower_Key;
               MXRecordTable (Bucket)(I) := TheRecord;
               Success := True;
            end if;
            exit when Success;
         end loop;
      end InsertMXRecord;

      procedure InsertSrvRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.Srv_Record_Type.SrvRecordType;
         Success   :    out Boolean)
      is
         Bucket    : RR_Type.NumBucketsIndexType;
         Lower_Key : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower (Key);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_Key);
         Success := False;
         for I in RR_Type.ReturnedRecordsIndexType loop
            if SrvRecordKeys (Bucket)(I) = RR_Type.BlankOwner then
               SrvRecordKeys (Bucket)(I) := Lower_Key;
               SrvRecordTable (Bucket)(I) := TheRecord;
               Success := True;
            end if;
            exit when Success;
         end loop;
      end InsertSRVRecord;

      procedure InsertNSRecord
        (Key       : in     RR_Type.WireStringType;
         theRecord : in     RR_Type.NS_Record_Type.NSRecordType;
         Success   :    out Boolean)
      is
         Bucket    : RR_Type.NumBucketsIndexType;
         Lower_Key : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower (Key);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_Key);

         Success := False;
         for I in RR_Type.ReturnedRecordsIndexType loop
            if NSRecordKeys (Bucket)(I) = RR_Type.BlankOwner then
               NSRecordKeys (Bucket)(I) := Lower_Key;
               NSRecordTable (Bucket)(I) := TheRecord;
               Success := True;
            end if;
            exit when Success;
         end loop;
      end InsertNSRecord;

      procedure InsertNSecRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.NSec_Record_Type.NSecRecordType;
         Success   :    out Boolean)
      is
         Bucket    : RR_Type.NumBucketsIndexType;
         Lower_Key : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower (Key);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_Key);

         Success := False;
         for I in RR_Type.ReturnedRecordsIndexType loop
            if NSecRecordKeys (Bucket)(I) = RR_Type.BlankOwner then
               NSecRecordKeys (Bucket)(I) := Lower_Key;
               NSecRecordTable (Bucket)(I) := TheRecord;
               Success := True;
            end if;
            exit when Success;
         end loop;
      end InsertNSecRecord;

      procedure InsertPtrRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.Ptr_Record_Type.PtrRecordType;
         Success   :    out Boolean)
      is
         Bucket    : RR_Type.NumBucketsIndexType;
         Lower_Key : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower (Key);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_Key);

         Success := False;
         for I in RR_Type.ReturnedRecordsIndexType loop
            if PtrRecordKeys (Bucket)(I) = RR_Type.BlankOwner then
               PtrRecordKeys (Bucket)(I) := Lower_Key;
               PtrRecordTable (Bucket)(I) := TheRecord;
               Success := True;
            end if;
            exit when Success;
         end loop;
      end InsertPtrRecord;

      procedure InsertRRSigRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.RRSig_Record_Type.RRSigRecordType;
         Success   :    out Boolean)
      is
         Bucket    : RR_Type.NumBucketsIndexType;
         Lower_Key : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower (Key);
         --queries must be case-insensitive, so hash on Lower case version
         Bucket := Hash (Lower_Key);

         Success := False;
         for I in RR_Type.ReturnedRecordsIndexType loop
            if RRSigRecordKeys (Bucket)(I) = RR_Type.BlankOwner then
               RRSigRecordKeys (Bucket)(I) := Lower_Key;
               RRSigRecordTable (Bucket)(I) := TheRecord;
               Success := True;
            end if;
            exit when Success;
         end loop;
      end InsertRRSigRecord;

      procedure InsertSOARecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.SOA_Record_Type.SOARecordType;
         Success   :    out Boolean)
      is
         Bucket             : RR_Type.NumBucketsIndexType;
         ReturnedSOARecords : RR_Type.SOA_Record_Type.SOARecordBucketType;
         NumFound           : Natural;
         Lower_Key          : RR_Type.WireStringType;
      begin
         Lower_Key := To_Lower (Key);
         --ReturnedSOARecords :=
         --  RR_Type.SOA_Record_Type.SOARecordBucketType'
         --    (others => RR_Type.soa_record_type.BlanksoaRecord);
         --SOA records are special, can only have one per domain.  Enforce that
         --here.
         QuerySOARecords (Lower_Key, ReturnedSOARecords, NumFound);
         if NumFound > 0 then
            Success := False;
         else
            --queries must be case-insensitive, so hash on Lower case version
            Bucket := Hash (Lower_Key);

            Success := False;
            for I in RR_Type.ReturnedRecordsIndexType loop
               if SOARecordKeys (Bucket)(I) = RR_Type.BlankOwner then
                  SOARecordKeys (Bucket)(I) := Lower_Key;
                  SOARecordTable (Bucket)(I) := TheRecord;
                  Success := True;
               end if;
               exit when Success;
            end loop;
         end if;
      end InsertSOARecord;

   end DNS_Table_Type;

end DNS_Table_Pkg;
