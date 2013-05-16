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
-- UserToken.Interface
--
-- Description:
--    Provides access to the User Token via the Token Reader interface.
--
------------------------------------------------------------------

with BasicTypes,
     CertTypes,
     TokenTypes;
--# inherit
--#    BasicTypes,
--#    CertTypes,
--#    TokenTypes,
--#    Clock,
--#    ConfigData,
--#    AuditLog;

private package UserToken.Interface
--#
--# own        State,
--#            Status,
--#     in     Input,
--#        out Output;
--# initializes Status;
is


   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the token readers.
   --
   ------------------------------------------------------------------

   procedure Init ;
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out Status;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#           out State;
   --# derives Status,
   --#         State              from Status &
   --#         AuditLog.FileState,
   --#         AuditLog.State     from Status,
   --#                                 AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Polls the user token reader to update the recorded state
   --    of the reader - determines whether a token is present.
   --
   ------------------------------------------------------------------

   procedure Poll ;
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Input;
   --#        in out Status;
   --#        in out State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --# derives Status             from * &
   --#         State              from *,
   --#                                 Status,
   --#                                 Input &
   --#         AuditLog.FileState from *,
   --#                                 Status,
   --#                                 State,
   --#                                 AuditLog.State,
   --#                                 Clock.Now &
   --#         AuditLog.State     from *,
   --#                                 Status,
   --#                                 State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State;

   ------------------------------------------------------------------
   -- TheTokenPresence
   --
   -- Description:
   --    Returns whether a user token is present.
   --
   ------------------------------------------------------------------

   function TheTokenPresence return BasicTypes.PresenceT;
   --# global State;

   ------------------------------------------------------------------
   -- TheTokenID
   --
   -- Description:
   --    Returns the token ID of a present token.
   --
   ------------------------------------------------------------------

   function TheTokenID return TokenTypes.TokenIDT;
   --# global State;


   ------------------------------------------------------------------
   -- TheTokenTry
   --
   -- Description:
   --    Returns return whether the token is not present, bad or good.
   --
   ------------------------------------------------------------------

   function TheTokenTry return  TokenTypes.TryT;
   --# global State;


   ------------------------------------------------------------------
   -- GetCertificate
   --
   -- Description:
   --    Gets the specified certificate from the user token. If the token is
   --    found successfully then Found is set true. Any problems obtaining the
   --    certificate will cause Found to be set false.
   --
   ------------------------------------------------------------------

   procedure GetCertificate
     (CertType  : in     CertTypes.CertificateT;
      RawCert   :    out CertTypes.RawCertificateT;
      Found     :    out Boolean);
   --# global in     State;
   --#        in     Input;
   --#        in out Status;
   --# derives Status  from * &
   --#         Found   from Status,
   --#                      State,
   --#                      CertType &
   --#         RawCert from Status,
   --#                      State,
   --#                      Input,
   --#                      CertType;


   ------------------------------------------------------------------
   -- WriteAuthCertificate
   --
   -- Description:
   --    Writes the auth cert to the user token. If there are any problems
   --    then success is set to false.
   --
   ------------------------------------------------------------------

   procedure WriteAuthCertificate
     (RawCert   : in     CertTypes.RawCertificateT;
      Success   :    out Boolean);
   --# global in     State;
   --#        in out Status;
   --#           out Output;
   --# derives Status  from * &
   --#         Output  from Status,
   --#                      State,
   --#                      RawCert &
   --#         Success from Status,
   --#                      State;


end UserToken.Interface;
