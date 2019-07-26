------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency.All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd.under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- AuditTypes
--
-- Description:
--    Types associated with audit.
--
------------------------------------------------------------------

with CommonTypes;

package AuditTypes is

   --------------------------------------------------------------
   --  Element
   --
   --  Description:
   --     Corresponds to AUDIT_ELEMENT in Formal Design
   --
   --------------------------------------------------------------

   type ElementT is
      (StartUnenrolledTIS,
        StartEnrolledTIS,
        EnrolmentComplete,
        EnrolmentFailed,
        DisplayChanged,
        ScreenChanged,
        DoorClosed,
        DoorOpened,
        LatchLocked,
        LatchUnlocked,
        AlarmRaised,
        AlarmSilenced,
        TruncateLog,
        AuditAlarmRaised,
        AuditAlarmSilenced,
        UserTokenRemoved,
        UserTokenPresent,
        UserTokenInvalid,
        AuthCertValid,
        AuthCertInvalid,
        FingerDetected,
        FingerTimeout,
        FingerMatched,
        FingerNotMatched,
        AuthCertWritten,
        AuthCertWriteFailed,
        EntryPermitted,
        EntryTimeout,
        EntryDenied,
        AdminTokenPresent,
        AdminTokenValid,
        AdminTokenInvalid,
        AdminTokenExpired,
        AdminTokenRemoved,
        InvalidOpRequest,
        OperationStart,
        ArchiveLog,
        ArchiveComplete,
        ArchiveCheckFailed,
        UpdatedConfigData,
        InvalidConfigData,
        Shutdown,
        OverrideLock,
        SystemFault);

   function ElementT_Image (X : ElementT) return CommonTypes.StringF1L20 is
      (ElementT'Image (X));
   pragma Annotate (GNATprove, False_Positive,
                    "predicate check might fail",
                    "Image of enums of type ElementT are short strings starting at index 1");

   --------------------------------------------------------------
   --  Severity
   --
   --  Description:
   --     Corresponds to AUDIT_SEVERITY in Formal Design
   --
   --------------------------------------------------------------
   type SeverityT is (Information, Warning, Critical);

   --------------------------------------------------------------
   --  DescriptionText
   --
   --  Description:
   --     Corresponds to TEXT in Formal Design
   --
   --------------------------------------------------------------
   subtype DescriptionI is Positive range 1..150;
   subtype DescriptionT is String(DescriptionI);
   NoDescription : constant DescriptionT := DescriptionT'(others => ' ');

   --------------------------------------------------------------
   --  UserText
   --
   --  Description:
   --     Corresponds to USERTEXT in Formal Design
   --
   --------------------------------------------------------------
   subtype UserTextI is Positive range 1..50;
   subtype UserTextT is String(UserTextI);

   NoUser : constant UserTextT :=
     "NoUser                                            ";

   --------------------------------------------------------------
   --  SizeAuditElement
   --
   --  Description:
   --     The size of a single Audit Element in Bytes
   --     Corresponds to SizeAuditElement in Formal Design
   --
   --     The size of the individual fields is as follows:
   --         Time        :  21
   --         Severity    :   1
   --         Id          :   2
   --         Type        :  20
   --         User        :  50
   --         Description : 150
   --        ==================
   --                       244
   --         Separators  :  10
   --         End of Line :   2
   --        ==================
   --                       256
   --------------------------------------------------------------
   SizeAuditElement :constant := 256;

   --------------------------------------------------------------
   --  MaxSupportedLogSize
   --
   --  Description:
   --     The size of the largest supported log file in Bytes
   --     Corresponds to MaxSupportedLogSize in Formal Design
   --
   --------------------------------------------------------------
   MaxSupportedLogSize :constant := 2**22;
   type FileSizeT is new Integer range 0..MaxSupportedLogSize;

   MaxSupportedLogEntries : constant := MaxSupportedLogSize / SizeAuditElement;
   type AuditEntryCountT is range 0..MaxSupportedLogEntries;

end AuditTypes;
