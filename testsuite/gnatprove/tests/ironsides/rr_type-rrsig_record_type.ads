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
     DNS_Types;

use type Unsigned_Types.Unsigned32,
         Unsigned_Types.Unsigned16,
         Unsigned_Types.Unsigned8;

package RR_Type.RRSig_Record_Type is
   TimeStringLength : constant Natural := 14;
   --YYYYMMDDHHmmSS

   Max_Year         : constant natural := 2020;
   --seems reasonable to bound this is some way

   subtype TimeStringTypeIndex is Natural range 1 .. TimeStringLength;
   subtype TimeStringType is String (TimeStringTypeIndex);

   MaxRRSigLength : constant natural := (1024 * 4) / 3;
   -- =1365, * 4/3 due to Base64 expansion

   subtype RRSigStringTypeIndex is natural range 1 .. MaxRRSigLength;
   subtype RRSigStringType is String (RRSigStringTypeIndex);
   subtype SigLengthValueType is Natural range 0 .. MaxRRSigLength;

   type RRSigRecordType is new RR_Type.ResourceRecordType with record
      TypeCovered     : DNS_Types.Query_Type;
      Algorithm       : Unsigned_Types.Unsigned8; --will be 5 for RSA/SHA1
      NumLabels       : Unsigned_Types.Unsigned8;
      OrigTTL         : Unsigned_Types.Unsigned32;
      SigExpiration   : Unsigned_Types.Unsigned32;
      SigInception    : Unsigned_Types.Unsigned32;
      KeyTag          : Unsigned_Types.Unsigned16;
      SignerName      : RR_Type.DomainNameStringType;
      Signature       : RRSigStringType;
      SignatureLength : SigLengthValueType;
   end record;

   --placeholder for empty slots in hash table
   BlankRRSigRecord : constant RRSigRecordType :=
     RRSigRecordType'(TTLInSeconds    => 0,
                      Class           => RR_Type.Internet,
                      TypeCovered     => DNS_Types.Error,
                      Algorithm       => 0,
                      NumLabels       => 1,
                      OrigTTL         => 0,
                      SigExpiration   => 0,
                      SigInception    => 0,
                      KeyTag          => 0,
                      SignerName      => RR_Type.Spaces128,
                      Signature       => RR_Type.Spaces1024 &
                                         RR_Type.Spaces256 &
                                         RR_Type.Spaces64 &
                                         "                     ", -- 1365 spaces
                      SignatureLength => 0);

--hash table (2d array) for RRSIG records
   type RRSigRecordBucketType is array (RR_Type.ReturnedRecordsIndexType)
     of RRSigRecordType;

   type RRSigRecordHashTableType is array (RR_Type.NumBucketsIndexType)
     of RRSigRecordBucketType;

end RR_Type.RRSig_Record_Type;
