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

use type Unsigned_Types.Unsigned32,
         Unsigned_Types.Unsigned16;

package RR_Type.Mx_Record_Type is
   --sufficiently below 2^16-1 that we can detect too large values without
   --wraparound
   Max_Pref_Val : constant Unsigned_Types.Unsigned16 := 2**15 - 1;

   type MXRecordType is new RR_Type.ResourceRecordType with record
      Pref          : Unsigned_Types.Unsigned16; --change Max_Pref_Val above
                                                 --if this type changes
      MailExchanger : RR_Type.WireStringType;
   end record;

   --placeholder for empty slots in hash table
   BlankMXRecord : constant MXRecordType :=
     MXRecordType'(TTLInSeconds  => 0,
                   Class         => RR_Type.Internet,
                   Pref          => 0,
                   MailExchanger => "empty.MX.resource.record         " &
                                    RR_Type.Spaces32 &
                                    RR_Type.Spaces32 &
                                    RR_Type.Spaces32);

   --hash table (2d array) for MX records
   type MXRecordBucketType is array (RR_Type.ReturnedRecordsIndexType)
     of MXRecordType;

   type MXRecordHashTableType is array (RR_Type.NumBucketsIndexType)
     of MXRecordBucketType;

end RR_Type.Mx_Record_Type;
