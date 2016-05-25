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

with DNS_Types;

PACKAGE RR_Type.NSec_Record_Type IS
   MaxNumberOfRecordTypes: constant Natural := 32;

   subtype RecordTypeIndexValue is natural range 0 .. MaxNumberOfRecordTypes;
   subtype RecordTypeArrayIndex is natural range 1 .. MaxNumberOfRecordTypes;
   type RecordTypeArrayType is array (RecordTypeArrayIndex)
     of DNS_Types.Query_Type;

   MaxNumberOfBlocks: constant Natural := MaxNumberOfRecordTypes;
   subtype BlockNumberValue is Natural range 0 .. MaxNumberOfBlocks;
   subtype BlockNumberArrayIndex is Natural range 1 .. MaxNumberOfBlocks;
   type BlockNumberArrayType is array (BlockNumberArrayIndex) of DNS_Types.Byte;

   subtype BlockLengthValue is Positive Range 1..32;
   type BlockLengthArrayType is array (BlockNumberArrayIndex)
     of BlockLengthValue;

   subtype BitMapIndex is Positive range 1 .. BlockLengthValue'Last;
   type BitMapArrayType is array (BitMapIndex) of DNS_Types.Byte;
   type BitMapsArrayArrayType is array (BlockNumberArrayIndex)
     of BitMapArrayType;

   MaxRRDataLength : constant Natural :=
     ((((RR_Type.MaxDomainNameLength + 1) --how long a wire domain name
                                          --length can be
      + MaxNumberofBlocks) --how many blocks you can have
      + MaxNumberOfBlocks) --again for the block lengths
      + MaxNumberOfBlocks * BlockLengthValue'Last); --for the bitmaps

   type NSecRecordType is new RR_Type.ResourceRecordType with record
      NextDomainName      : RR_Type.WireStringType;
      RecordList          : RR_Type.LineFromFileType; --just a string, gets
                                                      --parsed into detailed
                                                      --info below

      --record type block and bitmap info, needed for when record goes out on
      --the wire
      NumberOfRecordTypes : RecordTypeIndexValue;
      RecordTypes         : RecordTypeArrayType;
      NumberOfBlocks      : BlockNumberValue;
      BlockNumbers        : BlockNumberArrayType;
      BlockLengths        : BlockLengthArrayType;
      BitMaps             : BitMapsArrayArrayType;
   end record;

   --placeholder for empty slots in hash table
   BlankNSecRecord : constant NSecRecordType :=
     NSecRecordType'(TTLInSeconds        => 0,
                     Class               => RR_Type.Internet,
                     NextDomainName      => " " & RR_Type.Spaces128,
                     RecordList          => RR_Type.Spaces256,
                     NumberOfRecordTypes => 0,
                     RecordTypes         =>
                       RecordTypeArrayType'(others => DNS_Types.Unimplemented),
                     NumberOfBlocks      => 0,
                     BlockNumbers        => BlockNumberArrayType'(others => 0),
                     BlockLengths        =>
                       BlockLengthArrayType'(others => BlockLengthValue'First),
                     BitMaps             =>
                       BitMapsArrayArrayType'(others =>
                                                BitMapArrayType'(others => 0)));

   --hash table (2d array) for NSec records
   type NSecRecordBucketType is array (RR_Type.ReturnedRecordsIndexType)
     of NSecRecordType;

   type NSecRecordHashTableType is array (RR_Type.NumBucketsIndexType)
     of NSecRecordBucketType;

end RR_Type.NSec_Record_Type;
