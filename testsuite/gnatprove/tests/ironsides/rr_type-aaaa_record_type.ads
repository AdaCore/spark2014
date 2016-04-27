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

package RR_Type.AAAA_Record_Type is

   MaxIPV6AddrLength: constant Integer := 8; --8 32-bit integers
   subtype IPV6AddrTypeIndex is Integer range 1 .. MaxIPV6AddrLength;
   type IPV6AddrType is array (IPV6AddrTypeIndex) of Unsigned_Types.Unsigned16;
   Invalid_IPV6_Addr : constant IPV6AddrType := IPV6AddrType'(others => 0);

   type AAAARecordType is new RR_Type.ResourceRecordType with record
      IPV6 : IPV6AddrType;
   end record;

   --placeholder for empty slots in hash table
   BlankAAAARecord : constant AAAARecordType :=
     AAAARecordType'(TTLInSeconds => 0,
                     Class        => RR_Type.Internet,
                     IPV6         => Invalid_IPV6_Addr);

   --hash table (2d array) for AAAA records
   type AAAARecordBucketType is array (RR_Type.ReturnedRecordsIndexType)
     of AAAARecordType;

   type AAAARecordHashTableType is array (RR_Type.NumBucketsIndexType)
     of AAAARecordBucketType;

end RR_Type.AAAA_Record_Type;
