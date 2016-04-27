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
     RR_Type;

package RR_Type.A_Record_Type is
   type ARecordType is new RR_Type.ResourceRecordType with record
      IPV4 : Unsigned_Types.Unsigned32;
   end record;

   Invalid_IPV4_Addr : constant Unsigned_Types.Unsigned32 := 0;

   --placeholder for empty slots in hash table
   BlankARecord : constant ARecordType :=
     ARecordType'(TTLInSeconds => 0,
                  Class        => RR_Type.Internet,
                  IPV4         => Invalid_IPV4_Addr);

   --hash table (2d array) for A records
   type ARecordBucketType is array (RR_Type.ReturnedRecordsIndexType)
     of ARecordType;

   type ARecordHashTableType is array (RR_Type.NumBucketsIndexType)
     of ARecordBucketType;

end RR_Type.A_Record_Type;
