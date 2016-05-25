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
use type Unsigned_Types.Unsigned32;

package RR_Type.SOA_Record_Type is
   type SOARecordType is new RR_Type.ResourceRecordType with record
      NameServer   : RR_Type.WireStringType;
      Email        : RR_Type.WireStringType;
      SerialNumber : Unsigned_Types.Unsigned32;
      Refresh      : Unsigned_Types.Unsigned32;
      Retry        : Unsigned_Types.Unsigned32;
      Expiry       : Unsigned_Types.Unsigned32;
      Minimum      : Unsigned_Types.Unsigned32;
   end record;

   Max_Serial_Val : constant Long_Long_Integer := 2**32-1;
   Max_Time_Val   : constant Long_Long_Integer := 2**32-1;

   --placeholder for empty slots in hash table
   BlankSOARecord : constant SOARecordType :=
     SOARecordType'(TTLInSeconds => 0,
                    Class        => RR_Type.Internet,
                    NameServer   => "empty.soa.resource.record        " &
                                    RR_Type.Spaces32 &
                                    RR_Type.Spaces32 &
                                    RR_Type.Spaces32,
                    Email        => "empty.soa.resource.record        " &
                                    RR_Type.Spaces32 &
                                    RR_Type.Spaces32 &
                                    RR_Type.Spaces32,
                    SerialNumber => 0,
                    Refresh      => 0,
                    Retry        => 0,
                    Expiry       => 0,
                    Minimum      => 0);

   --hash table (2d array) for soa records
   type SOARecordBucketType is array (RR_Type.ReturnedRecordsIndexType)
     of SOARecordType;

   type SOARecordHashTableType is array (RR_Type.NumBucketsIndexType)
     of SOARecordBucketType;

end RR_Type.SOA_Record_Type;
