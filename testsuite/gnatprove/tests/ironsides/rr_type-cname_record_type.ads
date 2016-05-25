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

package RR_Type.CName_Record_Type is

   type CNameRecordType is new RR_Type.ResourceRecordType with record
      CanonicalDomainName : RR_Type.WireStringType;
   end record;

   --placeholder for empty slots in hash table
   BlankCNameRecord : constant CNameRecordType :=
     CNameRecordType'(TTLInSeconds        => 0,
                      Class               => RR_Type.Internet,
                      CanonicalDomainName =>
                        "empty.CNAME.resource.record      " &
                        RR_Type.Spaces32 & RR_Type.Spaces32 & RR_Type.Spaces32);

   --hash table (2d array) for CName records
   type CNameRecordBucketType is array (RR_Type.ReturnedRecordsIndexType)
     of CNameRecordType;

   type CNameRecordHashTableType is array (RR_Type.NumBucketsIndexType)
     of CNameRecordBucketType;

end RR_Type.CName_Record_Type;
