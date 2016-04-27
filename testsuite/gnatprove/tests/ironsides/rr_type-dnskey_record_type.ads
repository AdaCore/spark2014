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

with Unsigned_Types;

use type Unsigned_Types.Unsigned16,
         Unsigned_Types.Unsigned8;

package RR_Type.DNSKey_Record_Type is
   MaxDNSKeyLength : constant natural := (1024 * 4) / 3;  -- =1365, * 4/3 due
                                                          --to Base64 expansion
   subtype KeyLengthValueType is Natural range 0 .. MaxDNSKeyLength;
   subtype DNSKeyStringTypeIndex is Natural range 1 .. MaxDNSKeyLength;
   subtype DNSKeyStringType is String (DNSKeyStringTypeIndex);
   type DNSKeyRecordType is new RR_Type.ResourceRecordType with record
      Flags     : Unsigned_Types.Unsigned16;
      Protocol  : Unsigned_Types.Unsigned8; --must be 3 for DNSSEC
      Algorithm : Unsigned_Types.Unsigned8; --will be 5 for RSA/SHA1
      Key       : DNSKeyStringType;
      KeyLength : KeyLengthValueType;
   end record;

   Max_8Bit_Val  : constant Long_Long_Integer := 2**8  - 1;
   Max_16Bit_Val : constant Long_Long_Integer := 2**16 - 1;

   --Ugh.  But what can you do?
   Spaces64   : constant String := Rr_Type.Spaces32 & Rr_Type.Spaces32;
   Spaces128  : constant String := Spaces64 & Spaces64;
   Spaces256  : constant String := Spaces128 & Spaces128;
   Spaces512  : constant String := Spaces256 & Spaces256;
   Spaces1024 : constant String := Spaces512 & Spaces512;
   --1365 spaces, see above
   BlankKey   : constant String := Spaces1024 &
                                   Spaces256  &
                                   Spaces64   &
                                   "                     ";

   --placeholder for empty slots in hash table
   BlankDNSKeyRecord : constant DNSKeyRecordType :=
     DNSKeyRecordType'(TTLInSeconds => 0,
                       Class        => RR_Type.Internet,
                       Flags        => 0,
                       Protocol     => 0,
                       Algorithm    => 0,
                       Key          => BlankKey,
                       KeyLength    => 0);

   --hash table (2d array) for DNSKey records
   type DNSKeyRecordBucketType is array (RR_Type.ReturnedRecordsIndexType) of
     DNSKeyRecordType;

   type DNSKeyRecordHashTableType is array (RR_Type.NumBucketsIndexType) of
     DNSKeyRecordBucketType;

end RR_Type.DNSKey_Record_Type;
