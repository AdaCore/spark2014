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

use type Unsigned_Types.Unsigned32,
         Unsigned_Types.Unsigned16;

package RR_Type.Srv_Record_Type is
   --sufficiently below 2^16 - 1 that we can detect too large values without
   --wraparound
   Max_Pref_Val   : constant Unsigned_Types.Unsigned16 := 2**15-1;
   Max_Weight_Val : constant Unsigned_Types.Unsigned16 := 2**15-1;
   Max_Port_Val   : constant Unsigned_Types.Unsigned16 := 2**15-1;

   type SrvRecordType is new RR_Type.ResourceRecordType with record
      Pref       : Unsigned_Types.Unsigned16;
      --change Max_Pref_Val above if this type changes

      Weight     : Unsigned_Types.Unsigned16;
      --change Max_Weight_Val above if this type changes

      PortNum    : Unsigned_Types.Unsigned16;
      --change Max_Port_Val above if this type changes
      ServerName : RR_Type.WireStringType;
   end record;

   --placeholder for empty slots in hash table
   BlankSrvRecord : constant SrvRecordType :=
     SrvRecordType'(TTLInSeconds => 0,
                    Class        => RR_Type.Internet,
                    Pref         => 0,
                    Weight       => 0,
                    PortNum      => 0,
                    ServerName   => "empty.SRV.resource.record        " &
                                    RR_Type.Spaces32 &
                                    RR_Type.Spaces32 & RR_Type.Spaces32);

   --hash table (2d array) for Srv records
   type SrvRecordBucketType is array (RR_Type.ReturnedRecordsIndexType)
     of SrvRecordType;

   type SrvRecordHashTableType is array (RR_Type.NumBucketsIndexType)
     of SrvRecordBucketType;

end RR_Type.Srv_Record_Type;
