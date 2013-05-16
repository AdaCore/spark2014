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
-- AdminToken.Interface
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

private package AdminToken.Interface
--#
--# own        State,
--#            Status,
--#     in     Input;
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
   --    Initialises the token reader.
   --
   ------------------------------------------------------------------

   procedure Init ;
   --# global in out Status;
   --#           out State;
   --# derives Status,
   --#         State  from Status;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Polls the admin token reader to update the recorded state
   --    of the reader - determines whether a token is present.
   --
   ------------------------------------------------------------------

   procedure Poll ;
   --# global in     Input;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out Status;
   --#        in out State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --# derives Status             from * &
   --#         State              from *,
   --#                                 Status,
   --#                                 Input &
   --#         AuditLog.FileState,
   --#         AuditLog.State     from *,
   --#                                 Status,
   --#                                 State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State;

   ------------------------------------------------------------------
   -- TheTokenPresence
   --
   -- Description:
   --    Returns whether an admin token is present.
   --
   ------------------------------------------------------------------

   function TheTokenPresence return BasicTypes.PresenceT;
   --# global State;

   ------------------------------------------------------------------
   -- TheTokenID
   --
   -- Description:
   --    Returns the token ID of a present admin token.
   --
   ------------------------------------------------------------------

   function TheTokenID return TokenTypes.TokenIDT;
   --# global State;


   ------------------------------------------------------------------
   -- TheTokenTry
   --
   -- Description:
   --    Returns return whether the admin token is not present,
   --    bad or good.
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


end AdminToken.Interface;
