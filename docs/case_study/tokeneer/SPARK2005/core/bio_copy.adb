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
with AuditLog,
     AuditTypes,
     BasicTypes,
     Bio.Interface;

with Unchecked_Conversion;
use type BasicTypes.Unsigned32T;

package body Bio
--# own Input is in Bio.Interface.Input;
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
   function ValueOf(Code : ReturnT) return BasicTypes.Unsigned32T
   is
   --# hide ValueOf;
      function CodeToVal is
         new Unchecked_Conversion(ReturnT, BasicTypes.Unsigned32T);
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
   function GetReturnCode (ReturnVal : BasicTypes.Unsigned32T)
      return ReturnT
   is
      Result : ReturnT := InternalError;
   begin
      for Code in ReturnT loop
         --# assert ReturnT'First <= Code and
         --#        Code <= ReturnT'Last and
         --#        Result = InternalError;
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
     (Text        : String;
      ReturnValue : BasicTypes.Unsigned32T) return AuditTypes.DescriptionT
   is
      Result : AuditTypes.DescriptionT := AuditTypes.NoDescription;
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
      procedure SetResultString
      --# global in     Text;
      --#        in     TheCodeName;
      --#        in     ReturnValue;
      --#        in out Result;
      --# derives Result from *,
      --#                     Text,
      --#                     TheCodeName,
      --#                     ReturnValue;
      is
         --# hide SetResultString;

         FullString : String := Text & ": "
           & ReturnT'Image(TheCodeName) & " ( "
           & BasicTypes.Unsigned32T'Image(ReturnValue) & " )";
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

   procedure Poll(FingerPresent :    out BasicTypes.PresenceT)
   --# global in Interface.Input;
   --# derives FingerPresent from Interface.Input;
   is
   begin
      FingerPresent := Interface.IsSamplePresent;
   end Poll;


   ------------------------------------------------------------------
   -- Verify
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Verify(Template       : in     IandATypes.TemplateT;
                    MaxFAR         : in     IandATypes.FarT;
                    MatchResult    :    out IandATypes.MatchResultT;
                    AchievedFAR    :    out IandATypes.FarT)
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Interface.Input;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Template,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Interface.Input &
   --#         MatchResult        from Template,
   --#                                 MaxFAR,
   --#                                 Interface.Input &
   --#         AchievedFAR        from Template,
   --#                                 Interface.Input;
   is
      NumericReturn : BasicTypes.Unsigned32T;
   begin
      Interface.Verify(Template     => Template,
                       MaxFAR       => MaxFAR,
                       MatchResult  => MatchResult,
                       AchievedFAR  => AchievedFAR,
                       BioReturn    => NumericReturn);

      if NumericReturn /= ValueOf(BioAPIOk) then
         -- An error occurred, overwrite match information.
         MatchResult := IandATypes.NoMatch;
         AuditLog.AddElementToLog
           (ElementID    => AuditTypes.SystemFault,
            Severity     => AuditTypes.Warning,
            User         => AuditTypes.NoUser,
            Description  => MakeDescription ("Biometric device failure ",
                                             NumericReturn));
         end if;
   end Verify;


   ------------------------------------------------------------------
   -- Flush
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Flush
   --# global in Interface.Input;
   --# derives null from Interface.Input;
   is
   begin
      Interface.Flush;
   end Flush;

end Bio;
