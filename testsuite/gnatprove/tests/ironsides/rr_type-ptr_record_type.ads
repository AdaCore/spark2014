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

package RR_Type.Ptr_Record_Type is
   type PtrRecordType is new RR_Type.ResourceRecordType with record
      DomainName : RR_Type.WireStringType;
   end record;

   --placeholder for empty slots in hash table
   BlankPtrRecord : constant PtrRecordType :=
     PtrRecordType'(TTLInSeconds => 0,
                    Class        => RR_Type.Internet,
                    DomainName   => "empty.PTR.resource.record        " &
                                    RR_Type.Spaces32 &
                                    RR_Type.Spaces32 &
                                    RR_Type.Spaces32);

   --hash table (2d array) for Ptr records
   type PtrRecordBucketType is array (RR_Type.ReturnedRecordsIndexType)
     of PtrRecordType;

   type PtrRecordHashTableType is array (RR_Type.NumBucketsIndexType)
     of PtrRecordBucketType;

end RR_Type.Ptr_Record_Type;
