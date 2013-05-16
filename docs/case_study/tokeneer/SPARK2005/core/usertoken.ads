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
-- UserToken
--
-- Description:
--    Manages the interface to the User Token and maintains the
--    internal view of the contents of the user token.
--
------------------------------------------------------------------

with AuditTypes,
     IandATypes,
     PrivTypes;
--# inherit
--#    AuditTypes,
--#    BasicTypes,
--#    CertTypes,
--#    Cert.ID,
--#    Cert.Attr.Priv,
--#    Cert.Attr.IandA,
--#    Cert.Attr.Auth,
--#    CertProcessing,
--#    CertificateStore,
--#    Clock,
--#    ConfigData,
--#    CryptoTypes,
--#    AuditLog,
--#    KeyStore,
--#    IandATypes,
--#    PrivTypes,
--#    TokenTypes;

package UserToken
--# own State,
--#     Status,
--#     in Input,
--#     out Output;
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
   --    Initialises the user token reader.
   --
   -- Traceunit: C.UserToken.Init
   -- Traceto: FD.TIS.TISStartup
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
   --    Polls the external reader, and also the token if present, and
   --    updates State accordingly. A Card is only considered present
   --    once communications have been initiated, and the token ID has been
   --    extracted.
   --    May raise a System Fault.
   --
   -- Traceunit : C.UserToken.Poll
   -- Traceto : FD.Interface.TISPoll
   ------------------------------------------------------------------
   procedure Poll;
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
   -- UpdateAuthCert
   --
   -- Description:
   --    Updates token with locally stored (Auth Cert) data.
   --    May raise a System Fault.
   --
   -- Traceunit : C.UserToken.UpdateAuthCert
   -- Traceto : FD.Interface.UpdateToken
   ------------------------------------------------------------------
   procedure UpdateAuthCert (Success : out Boolean);
   --# global in     State;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     KeyStore.Store;
   --#        in out Status;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#           out Output;
   --# derives Status,
   --#         Success,
   --#         Output             from Status,
   --#                                 State,
   --#                                 KeyStore.Store &
   --#         AuditLog.FileState from *,
   --#                                 State,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 KeyStore.Store &
   --#         AuditLog.State     from *,
   --#                                 State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 KeyStore.Store;


   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Description:
   --    Returns the user associated with the current token.
   --
   -- Traceunit : C.UserToken.ExtractUser
   -- Traceto : FD.AuditLog.ExtractUser
   ------------------------------------------------------------------
   function ExtractUser return AuditTypes.UserTextT;
   --# global State;

   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Description:
   --    Returns True extactly when the toke is present
   --
   -- Traceunit : C.UserToken.IsPresent
   -- Traceto : FD.RealWorld.State
   ------------------------------------------------------------------
   function IsPresent return Boolean;
   --# global State;

   ------------------------------------------------------------------
   -- ReadAndCheckAuthCert
   --
   -- Description:
   --    Reads the ID and Auth certs from the token, extracts the data
   --    from them and checks that the data is OK as defined by
   --    UserTokenWithOKAuthCert.
   --    May raise a System Fault.
   --
   -- Traceunit : C.UserToken.ReadAndCheckAuthCert
   -- Traceto : FD.UserToken.UserTokenWithOKAuthCert
   ------------------------------------------------------------------
   procedure ReadAndCheckAuthCert(AuthCertOK :    out Boolean);
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Input;
   --#        in     KeyStore.Store;
   --#        in     Clock.CurrentTime;
   --#        in     KeyStore.State;
   --#        in out Status;
   --#        in out State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --# derives State,
   --#         AuthCertOK         from Status,
   --#                                 State,
   --#                                 Input,
   --#                                 KeyStore.Store,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.State &
   --#         AuditLog.FileState,
   --#         AuditLog.State     from Status,
   --#                                 State,
   --#                                 AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Input,
   --#                                 KeyStore.Store &
   --#         Status             from *,
   --#                                 State;

   ------------------------------------------------------------------
   -- ReadAndCheck
   --
   -- Description:
   --    Reads the ID, IandA and Priv certs from the certificate,
   --    extracts the data
   --    from them and checks that the data is OK as defined by
   --    UserTokenOK.
   --    May raise a System Fault.
   --
   -- Traceunit : C.UserToken.ReadAndCheck
   -- Traceto : FD.UserToken.UserTokenOK
   -- Traceto : FD.UserToken.UserTokenNotOK
   ------------------------------------------------------------------
   procedure ReadAndCheck
     (Description :    out AuditTypes.DescriptionT;
      TokenOK     :    out Boolean);
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Input;
   --#        in     KeyStore.Store;
   --#        in     Clock.CurrentTime;
   --#        in out Status;
   --#        in out State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --# derives State,
   --#         TokenOK,
   --#         Description        from Status,
   --#                                 State,
   --#                                 Input,
   --#                                 KeyStore.Store,
   --#                                 Clock.CurrentTime &
   --#         AuditLog.FileState,
   --#         AuditLog.State     from Status,
   --#                                 State,
   --#                                 AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Input,
   --#                                 KeyStore.Store &
   --#         Status             from *,
   --#                                 State;


   ------------------------------------------------------------------
   -- AddAuthCert
   --
   -- Description:
   --    Constructs the contents of a new AuthCert.
   --    Success is based on whether a serial number could be issued
   --    or not.
   --
   -- Traceunit : C.UserToken.AddAuthCert
   -- Traceto   : FD.UserToken.AddAuthCertToUserToken
   ------------------------------------------------------------------
   procedure AddAuthCert( Success : out Boolean);
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Clock.CurrentTime;
   --#        in     KeyStore.State;
   --#        in     CertificateStore.State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#        in out State;
   --# derives State   from *,
   --#                      ConfigData.State,
   --#                      Clock.CurrentTime,
   --#                      KeyStore.State,
   --#                      CertificateStore.State &
   --#         AuditLog.FileState,
   --#         AuditLog.State     from AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 CertificateStore.State &
   --#         Success from CertificateStore.State;
   --# pre KeyStore.PrivateKeyPresent(KeyStore.State);

   ------------------------------------------------------------------
   -- GetIandATemplate
   --
   -- Description:
   --    obtains the biometric template associated with the token.
   --
   -- Traceunit : C.UserToken.GetIandATemplate
   -- Traceto : FD.UserEntry.ValidateFingerOK
   -- Traceto : FD.UserEntry.ValidateFingerFail
   ------------------------------------------------------------------
   function GetIandATemplate return IandATypes.TemplateT;
   --# global State;


   ------------------------------------------------------------------
   -- GetClass
   --
   -- Description:
   --    obtains the class value for the Priv certificate.
   --
   -- Traceunit : C.UserToken.GetClass
   -- Traceto : FD.Certificate.NewAuthCert
   ------------------------------------------------------------------
   function GetClass return PrivTypes.ClassT;
   --# global State;


   ------------------------------------------------------------------
   -- Clear
   --
   -- Description:
   --    Clears UserToken.State certificate information
   --
   -- Traceunit : C.UserToken.Clear
   -- Traceto : FD.UserToken.Clear
   ------------------------------------------------------------------
   procedure Clear;
   --# global in out State;
   --# derives State from *;


end UserToken;
