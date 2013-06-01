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
-- TokenReader
--
-- Description:
--    Package maintaining and controlling the token readers.
--
------------------------------------------------------------------
with BasicTypes;
with CertTypes;
with TokenTypes;

--# inherit
--#    AuditLog,
--#    AuditTypes,
--#    BasicTypes,
--#    ConfigData,
--#    Clock,
--#    CertTypes,
--#    TokenTypes;

package TokenReader
--# own State,
--#     Status,
--#     in  Input,
--#     out Output;
--# initializes Status;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type ReaderT is (User, Admin);



   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the token readers.
   --
   -- traceunit : C.TokenReader.Init
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
   --    Polls the specified token reader to update the recorded state
   --    of the reader - determines whether a token is present.
   --    May raise a system fault.
   --
   -- traceunit : C.TokenReader.Poll
   ------------------------------------------------------------------

   procedure Poll ( Reader : in ReaderT) ;
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Input;
   --#        in out Status;
   --#        in out State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --# derives AuditLog.FileState,
   --#         AuditLog.State     from Status,
   --#                                 State,
   --#                                 AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Reader &
   --#         Status             from * &
   --#         State              from *,
   --#                                 Status,
   --#                                 Input,
   --#                                 Reader;

   ------------------------------------------------------------------
   -- TheTokenPresence
   --
   -- Description:
   --    Returns whether a token is present.
   --
   -- traceunit : C.TokenReader.TheTokenPresence
   ------------------------------------------------------------------

   function TheTokenPresence (Reader  :  ReaderT) return BasicTypes.PresenceT;
   --# global State;

   ------------------------------------------------------------------
   -- TheTokenID
   --
   -- Description:
   --    Returns the token ID of a present token.
   --
   -- traceunit : C.TokenReader.TheTokenID
   ------------------------------------------------------------------

   function TheTokenID (Reader : ReaderT) return  TokenTypes.TokenIDT;
   --# global State;


   ------------------------------------------------------------------
   -- TheTokenTry
   --
   -- Description:
   --    Returns return whether the token is not present, bad or good.
   --
   -- traceunit : C.TokenReader.TheTokenTry
   ------------------------------------------------------------------

   function TheTokenTry (Reader : ReaderT) return  TokenTypes.TryT;
   --# global State;


   ------------------------------------------------------------------
   -- GetCertificate
   --
   -- Description:
   --    Gets the specified certificate from the token. If the token is
   --    found successfully then Found is set true. Any problems obtaining the
   --    certificate will cause Found to be set false.
   --
   -- traceunit : C.TokenReader.GetCertificate
   ------------------------------------------------------------------

   procedure GetCertificate (Reader    : in     ReaderT;
                             CertType  : in     CertTypes.CertificateT;
                             RawCert   :    out CertTypes.RawCertificateT;
                             Found     :    out Boolean);
   --# global in     State;
   --#        in     Input;
   --#        in out Status;
   --# derives Status  from * &
   --#         Found   from Status,
   --#                      State,
   --#                      Reader,
   --#                      CertType &
   --#         RawCert from Status,
   --#                      State,
   --#                      Input,
   --#                      Reader,
   --#                      CertType;


   ------------------------------------------------------------------
   -- WriteAuthCertificate
   --
   -- Description:
   --    Writes the auth cert to the user token. If there are any problems
   --    then success is set to false.
   --
   -- traceunit : C.TokenReader.GetCertificate
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


end TokenReader;
