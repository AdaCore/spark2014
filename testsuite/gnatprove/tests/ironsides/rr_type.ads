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

package RR_Type IS
   pragma Elaborate_Body (RR_Type);
   type classType is (Internet,
                      CS,
                      CH,
                      HS);
   --Internet because IN is a reserved word the things that can appear in a
   --resource record

   type RRItemType is (DomainNameOrTimeSpec,
                       Number,
                       Class,
                       RecordIndicator,
                       IPV4,
                       IPV6,
                       LParen,
                       RParen,
                       Control,
                       Comment,
                       Other);
   --maybe this should be in a separate type package?
   MaxLineLength : constant Natural := 255 + 1;  --256 is what we tell the user
   subtype LineLengthIndex is Integer range 1 .. MaxLineLength;
   subtype LineFromFileType is String (LineLengthIndex);
   BlankLine : constant LineFromFileType := LineFromFileType'(others => ' ');

   MaxDomainNameLength: constant Integer := 128;
   subtype DomainNameStringTypeIndex is Integer range 1 .. MaxDomainNameLength;
   subtype DomainNameStringType is String (DomainNameStringTypeIndex);
   BlankDomainName : constant DomainNameStringType :=
     DomainNameStringType'(others => ' ');

   --wire version of a domain name is one character longer
   subtype WireStringTypeIndex is Integer range 1 .. MaxDomainNameLength + 1;
   subtype WireStringType is String (WireStringTypeIndex);
   BlankWire : constant WireStringType := WireStringType'(others => ' ');
   Spaces32 : constant String := "                                ";

   --these constants are needed in child packages
   Max_8Bit_Val  : constant Long_Long_Integer := 2**8  - 1;
   Max_16Bit_Val : constant Long_Long_Integer := 2**16 - 1;
   Max_32Bit_Val : constant Long_Long_Integer := 2**32 - 1;


   --Ugh.  But what can you do?
   Spaces64   : constant String := Spaces32 & Spaces32;
   Spaces128  : constant String := Spaces64 & Spaces64;
   Spaces256  : constant String := Spaces128 & Spaces128;
   Spaces512  : constant String := Spaces256 & Spaces256;
   Spaces1024 : constant String := Spaces512 & Spaces512;

   procedure AppendDomainNames
     (Left    : in out DomainNameStringType;
      Right   : in     DomainNameStringType;
      Success : in out Boolean)
   with Depends => ((Left, Success) => (Left, Right, Success));

   function WireNameLength (Name : in WireStringType) return WireStringTypeIndex
   with Post =>
     WireNameLength'Result = MaxDomainNameLength + 1 or
     (Name (WireNameLength'Result) = Character'Val (0) and
        (for all Q in DomainNameStringTypeIndex
         range 1 .. WireNameLength'Result - 1 =>
           Name (Q) /= Character'Val (0)));

   function DomainNameLength
     (Name : in DomainNameStringType)
      return DomainNameStringTypeIndex
   with Post =>
     (DomainNameLength'Result = 1 and (Name (1) = ' ' or Name (2) = ' ')) or
     DomainNameLength'Result = MaxDomainNameLength or
     (Name (DomainNameLength'Result + 1) = ' ' and
        (for all Q in DomainNameStringTypeIndex
         range 1 .. DomainNameLength'Result =>
           Name (Q) /= ' '));

   function ConvertDomainNameToWire
     (DomainNameVersion: in DomainNameStringType)
      return WireStringType
   with Post =>
     (for all I in DomainNameStringTypeIndex =>
        Character'Pos (ConvertDomainNameToWire'Result (I)) >= 0 and
        Character'Pos (ConvertDomainNameToWire'Result (I)) <= 255);

   function ConvertStringToDomainName
     (S : in String)
      return DomainNameStringType
   with Pre => S'Length <= MaxDomainNameLength;

   function ConvertStringToWire (S : in String) return WireStringType
   with Pre => S'Length <= MaxDomainNameLength;

   -- top level record, fields are common to all subrecords
   type ResourceRecordType is tagged record
      TTLInSeconds : Unsigned_Types.Unsigned32;
      Class        : ClassType;
   end record;

   BlankOwner : constant WireStringType :=
     ASCII.NUL & "empty.A.resource.record         " & Spaces32 & Spaces32 &
     Spaces32;

   --maximum bucket size in hash table (num cols in 2d array),
   --also max num records returned from query
   MaxNumRecords : constant Integer := 64;
   subtype ReturnedRecordsIndexType is Integer range 1 .. MaxNumRecords;
   subtype NumberOfRecordsType is Integer range 0 .. MaxNumRecords;

   --number of buckets in hash table (num rows in 2d array)
   NumBuckets : constant Integer := 64;
   subtype NumBucketsIndexType is Integer range 1 .. NumBuckets;

   type OwnerRecordBucketType is array (ReturnedRecordsIndexType)
     of WireStringType;

   type OwnerHashTableType is array (NumBucketsIndexType)
     of OwnerRecordBucketType;

end RR_Type;
