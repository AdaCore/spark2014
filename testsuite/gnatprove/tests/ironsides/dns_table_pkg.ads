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

with Unsigned_Types,
     RR_Type,
     RR_Type.A_Record_Type,
     RR_Type.AAAA_Record_Type,
     RR_Type.CName_Record_Type,
     RR_Type.DNSKey_Record_Type,
     RR_Type.MX_Record_Type,
     RR_Type.NS_Record_Type,
     RR_Type.NSec_Record_Type,
     RR_Type.Ptr_Record_Type,
     RR_Type.RRSig_Record_Type,
     RR_Type.SOA_Record_Type,
     RR_Type.Srv_Record_Type;

use type Unsigned_Types.Unsigned32;

--need these for equality operator in package body
use type RR_Type.A_Record_Type.ARecordType,
         RR_Type.AAAA_Record_Type.AAAARecordType,
         RR_Type.CName_Record_Type.CNameRecordType,
         RR_Type.DNSKey_Record_Type.DNSKeyRecordType,
         RR_Type.MX_Record_Type.MXRecordType,
         RR_Type.Srv_Record_Type.SrvRecordType,
         RR_Type.NS_Record_Type.NSRecordType,
         RR_Type.NSec_Record_Type.NSecRecordType,
         RR_Type.Ptr_Record_Type.PtrRecordType,
         RR_Type.RRSig_Record_Type.RRSigRecordType,
         RR_Type.SOA_Record_Type.SOARecordType;

--in case debugging IO needed
--with Ada.Text_IO, Ada.Integer_Text_IO;


package DNS_Table_Pkg is

   protected type DNS_Table_Type is
      pragma Priority (0);

      procedure InsertARecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.A_Record_Type.ARecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure InsertAAAARecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.AAAA_Record_Type.AAAARecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure InsertCNameRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_type.CName_Record_Type.CNameRecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure InsertDNSKeyRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure InsertMXRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.MX_Record_Type.MXRecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure InsertSrvRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.Srv_Record_Type.SrvRecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure InsertNSRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.NS_Record_Type.NSRecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure InsertNSecRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.NSec_Record_Type.NSecRecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure InsertPtrRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.Ptr_Record_Type.PtrRecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure InsertRRSigRecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_Type.RRSig_Record_Type.RRSigRecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure InsertSOARecord
        (Key       : in     RR_Type.WireStringType;
         TheRecord : in     RR_type.SOA_Record_Type.SOARecordType;
         Success   :    out Boolean)
      with Global  => null,
           Depends => (DNS_Table_Type =>+ (Key, TheRecord),
                       Success => (DNS_Table_Type, Key));

      procedure QueryARecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.A_Record_Type.ARecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

      -- to support RFC 4074
      procedure CountARecords
        (DomainName : in     RR_Type.WireStringType;
         HowMany    :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => (HowMany => (DNS_Table_Type, DomainName),
                       DNS_Table_Type =>+ null);

      procedure CountAAAARecords
        (DomainName : in     RR_Type.WireStringType;
         HowMany    :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => (HowMany => (DNS_Table_Type, DomainName),
                       DNS_Table_Type =>+ null);

      procedure QueryAAAARecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.AAAA_Record_Type.AAAARecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

      procedure QueryCNameRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.CName_Record_Type.CNameRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

      procedure QueryDNSKeyRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.DNSKey_Record_Type.DNSKeyRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

      procedure QueryMXRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.MX_Record_Type.MXRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

      procedure QuerySRVRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.Srv_Record_Type.SrvRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

      procedure QueryNSRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.NS_Record_Type.NSRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

      procedure QueryNSecRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.NSec_Record_Type.NSecRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

      procedure QueryPTRRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.Ptr_Record_Type.PtrRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

      procedure QueryRRSIGRecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.RRSig_Record_Type.RRSigRecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

      procedure QuerySOARecords
        (DomainName      : in     RR_Type.WireStringType;
         ReturnedRecords :    out RR_Type.SOA_Record_Type.SOARecordBucketType;
         HowMany         :    out RR_Type.NumberOfRecordsType)
      with Global  => null,
           Depends => ((HowMany,
                        ReturnedRecords) => (DNS_Table_Type,
                                             DomainName),
                       DNS_Table_Type =>+ null);

   private
      ARecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      ARecordTable : RR_Type.A_Record_Type.ARecordHashTableType :=
        RR_Type.A_Record_Type.ARecordHashTableType'
          (others => RR_Type.A_Record_Type.ARecordBucketType'
                       (others => RR_Type.A_Record_Type.BlankARecord));

      AAAARecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      AAAARecordTable : RR_Type.AAAA_Record_Type.AAAARecordHashTableType :=
        RR_Type.AAAA_Record_Type.AAAARecordHashTableType'
          (others => RR_Type.AAAA_Record_Type.AAAARecordBucketType'
                       (others => RR_Type.AAAA_Record_Type.BlankAAAARecord));

      CNameRecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      CNameRecordTable : RR_Type.CName_Record_Type.CNameRecordHashTableType :=
        RR_Type.CName_Record_Type.CNameRecordHashTableType'
          (others => RR_Type.CName_Record_Type.CNameRecordBucketType'
                       (others => RR_Type.CName_Record_Type.BlankCNameRecord));

      DNSKeyRecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      DNSKeyRecordTable : RR_Type.DNSKey_Record_Type.DNSKeyRecordHashTableType :=
        RR_Type.DNSKey_Record_Type.DNSKeyRecordHashTableType'
          (others => RR_Type.DNSKey_Record_Type.DNSKeyRecordBucketType'
                       (others => RR_Type.DNSKey_Record_Type.BlankDNSKeyRecord));

      MXRecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      MXRecordTable : RR_Type.MX_Record_Type.MXRecordHashTableType :=
        RR_Type.MX_Record_Type.MXRecordHashTableType'
          (others => RR_Type.MX_Record_Type.MXRecordBucketType'
                       (others => RR_Type.MX_Record_Type.BlankMXRecord));

      SrvRecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      SrvRecordTable : RR_Type.Srv_Record_Type.SrvRecordHashTableType :=
        RR_Type.Srv_Record_Type.SrvRecordHashTableType'
          (others => RR_Type.Srv_Record_Type.SrvRecordBucketType'
                       (others => RR_Type.Srv_Record_Type.BlankSrvRecord));

      NSRecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      NSRecordTable : RR_Type.NS_Record_Type.NSRecordHashTableType :=
        RR_Type.NS_Record_Type.NSRecordHashTableType'
          (others => RR_Type.NS_Record_Type.NSRecordBucketType'
                       (others => RR_Type.NS_Record_Type.BlankNSRecord));

      NSecRecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      NSecRecordTable : RR_Type.NSec_Record_Type.NSecRecordHashTableType :=
        RR_Type.NSec_Record_Type.NSecRecordHashTableType'
          (others => RR_Type.NSec_Record_Type.NSecRecordBucketType'
                       (others => RR_Type.NSec_Record_Type.BlankNSecRecord));

      PtrRecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      PtrRecordTable : RR_Type.Ptr_Record_Type.PtrRecordHashTableType :=
        RR_Type.Ptr_Record_Type.PtrRecordHashTableType'
          (others => RR_Type.Ptr_Record_Type.PtrRecordBucketType'
                       (others => RR_Type.Ptr_Record_Type.BlankPtrRecord));

      RRSigRecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      RRSigRecordTable : RR_Type.RRSig_Record_Type.RRSigRecordHashTableType :=
        RR_Type.RRSig_Record_Type.RRSigRecordHashTableType'
          (others => RR_Type.RRSig_Record_Type.RRSigRecordBucketType'
                       (others => RR_Type.RRSig_Record_Type.BlankRRSigRecord));

      SOARecordKeys : RR_Type.OwnerHashTableType :=
        RR_Type.OwnerHashTableType'
          (others => RR_Type.OwnerRecordBucketType'
                       (others => RR_Type.BlankOwner));

      SOARecordTable : RR_Type.SOA_Record_Type.SOARecordHashTableType :=
        RR_type.SOA_Record_Type.SOARecordHashTableType'
          (others => RR_Type.SOA_Record_Type.SOARecordBucketType'
                       (others => RR_Type.SOA_Record_Type.BlankSOARecord));
   end DNS_Table_Type;

   --THIS IS THE NAME SERVER HASH TABLE
   DNS_Table: DNS_Table_Type;

end DNS_Table_Pkg;
