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

--all error diagnostic I/O goes here.  Spark I/O libraries are a pain,
--use regular Ada I/O instead and just hide it from the prying eyes of the examiner.
with RR_Type,
     Unsigned_Types;

package Error_Msgs is

   procedure PrintUnsupportedRecordWarning
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   with Depends => (null => (CurrentLine, Length, LineCount));

   procedure PrintZeroTTLWarning
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   with Depends => (null => (CurrentLine, Length, LineCount));

   procedure PrintBlankOriginWarning
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   with Depends => (null => (CurrentLine, Length, LineCount));

   procedure PrintTooManyRecordTypesInNSecRecordWarning
     (LineCount : in Unsigned_Types.Unsigned32)
   with Depends => (null => LineCount);

   procedure PrintParseErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   with Depends => (null => (CurrentLine, Length, LineCount));

   procedure PrintLineLengthErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   with Depends => (null => (CurrentLine, Length, LineCount));

   procedure PrintSOARecordErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   with Depends => (null => (CurrentLine, Length, LineCount));

   procedure PrintMissingRecordTypeErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   with Depends => (null => (CurrentLine, Length, LineCount));

   procedure PrintAppendDomainLengthErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   with Depends => (null => (CurrentLine, Length, LineCount));

   procedure PrintDomainLengthErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      BegIdx      : in Natural;
      EndIdx      : in Natural)
   with Depends => (null => (BegIdx, CurrentLine, EndIdx));

   procedure PrintRRStringLengthErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      BegIdx      : in Natural;
      EndIdx      : in Natural)
   with Depends => (null => (BegIdx, CurrentLine, EndIdx));

   procedure PrintDNSTableFullInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      LineCount   : in Unsigned_Types.Unsigned32)
   with Depends => (null => (CurrentLine, LineCount));

   procedure PrintKeyLengthErrorInfo
     (CurrentLine : in RR_Type.LineFromFileType;
      Length      : in Natural;
      LineCount   : in Unsigned_Types.Unsigned32)
   with Depends => (null => (CurrentLine, Length, LineCount));

   procedure PrintMissingSOARecordInfo
   with Depends => null;

end Error_Msgs;
