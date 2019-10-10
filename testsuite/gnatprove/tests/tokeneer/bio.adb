------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- Bio
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with Bio.Interfac,
     CommonTypes;

with Unchecked_Conversion;

use type CommonTypes.Unsigned32T;
with Clock;

package body Bio
  with Refined_State => (Input => Bio.Interfac.Input)
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   -- Verify returns an unsigned 32 bit 'return value', representing
   -- the possible faults that could occur. ReturnT models the possible errors
   -- and local procedure GetReturnCode converts the returned value
   -- into a ReturnT type.

   type ReturnT is
      (BioApiOk,
       -- High Level framework errors:
       InternalError,
       MemoryError,
       FunctionFailed,
       InvalidData,
       BioApiNotInitialized,
       ModuleLoadFailed,
       ModuleUnloadFailed,
       -- BSP Level errors:
       BspInternalError,
       BspMemoryError,
       BspFunctionFailed,
       BspInvalidData,
       BspUnableToCapture,
       BspTimeoutExpired,
       BspBirSignatureFailure,
       BspInconsistentPurpose,
       -- Device Level Errors:
       DeviceLevelError);

   for ReturnT use   -- Error codes Values.
      (BioApiOk               => 16#0000#,
       InternalError          => 16#0001#,
       MemoryError            => 16#0002#,
       FunctionFailed         => 16#000A#,
       InvalidData            => 16#0046#,
       BioApiNotInitialized   => 16#0102#,
       ModuleLoadFailed       => 16#0116#,
       ModuleUnloadFailed     => 16#0118#,
       BspInternalError       => 16#1001#,
       BspMemoryError         => 16#1002#,
       BspFunctionFailed      => 16#100A#,
       BspInvalidData         => 16#1046#,
       BspUnableToCapture     => 16#1101#,
       BspTimeoutExpired      => 16#1103#,
       BspBirSignatureFailure => 16#1105#,
       BspInconsistentPurpose => 16#110D#,
       DeviceLevelError       => 16#2001#);

   for ReturnT'Size use 32;

   function ReturnT_Image (X : ReturnT) return CommonTypes.StringF1L1000 is
      (ReturnT'Image (X));
   pragma Annotate (GNATprove, False_Positive,
                    "predicate check might fail",
                    "Image of enums of type ReturnT are short strings starting at index 1");

   ------------------------------------------------------------------
   -- ValueOf
   --
   -- Description:
   --    Converts a ReturnT type to its numeric representation.
   --    Hidden from SPARK to allow unchecked conversion.
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function ValueOf (Code : ReturnT) return CommonTypes.Unsigned32T
   is
      function CodeToVal is
         new Unchecked_Conversion(ReturnT, CommonTypes.Unsigned32T);
   begin
      return CodeToVal(Code);
   end ValueOf;

   ------------------------------------------------------------------
   -- GetReturnCode
   --
   -- Description:
   --    Converts a supplied numeric return value to the
   --    correct enumeration. If the return value is not valid,
   --    the 'InternalError' literal is returned.
   --
   -- Implementation Notes:
   --    Loops over the enumerated type, and performs an unchecked
   --    conversion from the enumerated type to the numeric type.
   --    Exits when a match is made.
   ------------------------------------------------------------------
   function GetReturnCode (ReturnVal : CommonTypes.Unsigned32T)
      return ReturnT
   is
      Result : ReturnT := InternalError;
   begin
      for Code in ReturnT loop
         pragma Loop_Invariant (ReturnT'First <= Code and
                                Code <= ReturnT'Last and
                                Result = InternalError);
         if ReturnVal = ValueOf(Code) then
            Result := Code;
            exit;
         end if;
      end loop;
      return Result;
   end GetReturnCode;

   ------------------------------------------------------------------
   -- MakeDescription
   --
   -- Description:
   --    Produces a description for the Audit log from the
   --    supplied text and return value.
   --
   -- Implementation Notes:
   --    None
   ------------------------------------------------------------------
   function MakeDescription
     (Text        : CommonTypes.StringF1L1000;
      ReturnValue : CommonTypes.Unsigned32T)
     return AuditTypes.DescriptionT
     with Global => null;

   function MakeDescription
     (Text        : CommonTypes.StringF1L1000;
      ReturnValue : CommonTypes.Unsigned32T)
     return AuditTypes.DescriptionT

   is
      Result      : AuditTypes.DescriptionT := AuditTypes.NoDescription;
      TheCodeName : ReturnT;

      ------------------------------------------------------------------
      -- SetResultString
      --
      -- Description:
      --    Sets the Result string allowing for overflow.
      --
      -- Implementation Notes:
      --    None
      ------------------------------------------------------------------
      procedure SetResultString with
        Post => True  --  no contextual analysis needed
      is
         FullString : String := Text & ": "
           & ReturnT_Image(TheCodeName) & " ( "
           & CommonTypes.Unsigned32T'Image(ReturnValue) & " )";
      begin

         -- if the Full string is shorter then use it all otherwise
         -- truncate it.
         if FullString'Last <= AuditTypes.DescriptionI'Last then
            Result (1.. FullString'Last) := FullString;
         else
            Result := FullString (1 .. AuditTypes.DescriptionI'Last);
         end if;
      end SetResultString;

   begin

      TheCodeName := GetReturnCode (ReturnValue);

      SetResultString;

      return Result;

   end MakeDescription;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Poll (FingerPresent :    out CommonTypes.PresenceT)
     with Refined_Global  => (Input => Interfac.Input),
          Refined_Depends => (FingerPresent => Interfac.Input)
   is
   begin
      FingerPresent := Interfac.IsSamplePresent;
   end Poll;

   ------------------------------------------------------------------
   -- Verify
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Verify (Template    : in     IandATypes.TemplateT;
                     MaxFAR      : in     IandATypes.FarT;
                     MatchResult :    out IandATypes.MatchResultT;
                     AchievedFAR :    out IandATypes.FarT)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Interfac.Input),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State)),
          Refined_Depends => (AchievedFAR          => (Interfac.Input,
                                                       Template),
                              (AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.Input,
                                                       Template),
                              MatchResult          => (Interfac.Input,
                                                       MaxFAR,
                                                       Template))
   is
      NumericReturn : CommonTypes.Unsigned32T;
   begin

      Interfac.Verify(Template     => Template,
                      MaxFAR       => MaxFAR,
                      MatchResult  => MatchResult,
                      AchievedFAR  => AchievedFAR,
                      BioReturn    => NumericReturn);

#if SECURITY_DEMO
      --  back door: at midnight, allow any fingerprint to match
      declare
         use type Clock.MilliSecsT;
         Current_Time : constant Clock.TimeT := Clock.GetNow;
      begin
         if Current_Time.MilliSec = 0 then
            MatchResult := IandATypes.Match;
            return;
         end if;
      end;
#end if;

      if NumericReturn /= ValueOf(BioAPIOk) then
         -- An error occurred, overwrite match information.
         MatchResult := IandATypes.NoMatch;
         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => MakeDescription(
                                  "Biometric device failure ",
                                  NumericReturn)
                );
      end if;

   end Verify;

   ------------------------------------------------------------------
   -- Flush
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Flush
     with Refined_Global  => (Input => Interfac.Input),
          Refined_Depends => (null => Interfac.Input)
   is
   begin
      Interfac.Flush;
   end Flush;

end Bio;
