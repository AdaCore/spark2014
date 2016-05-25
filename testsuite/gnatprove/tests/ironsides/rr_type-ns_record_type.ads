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

package RR_Type.NS_Record_Type is
   type NSRecordType is new RR_Type.ResourceRecordType with record
      NameServer : RR_Type.WireStringType;
   end record;

   --placeholder for empty slots in hash table
   BlankNSRecord : constant NSRecordType :=
     NSRecordType'(TTLInSeconds => 0,
                   Class        => RR_Type.Internet,
                   NameServer   => "empty.NS.resource.record         " &
                                   RR_Type.Spaces32 &
                                   RR_Type.Spaces32 &
                                   RR_Type.Spaces32);

   --hash table (2d array) for NS records
   type NSRecordBucketType is array (RR_Type.ReturnedRecordsIndexType)
     of NSRecordType;

   type NSRecordHashTableType is array (RR_Type.NumBucketsIndexType)
     of NSRecordBucketType;

end RR_Type.NS_Record_Type;
