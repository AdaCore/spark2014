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

with AuditLog,
     AuditTypes,
     CommonTypes,
     Cert.Attr.Auth,
     Cert.Attr.IandA,
     Cert.Attr.Priv,
     Cert.ID,
     CertificateStore,
     CertProcessing,
     CertTypes,
     Clock,
     ConfigData,
     CryptoTypes,
     IandATypes,
     KeyStore,
     PrivTypes,
     TokenTypes;

use KeyStore;

package UserToken
  with Abstract_State => (State,
                          Status,
                          (Input  with External => Async_Writers),
                          (Output with External => Async_Readers)),
        Initializes   => (Status, Output)
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
   procedure Init
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      Output => State,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Status),
                      (State,
                       Status)             => Status);

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
   -- Traceto : FD.Interfac.TISPoll
   ------------------------------------------------------------------
   procedure Poll
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Input),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State,
                                 Status)),
          Depends => (AuditLog.FileState =>+ (AuditLog.State,
                                              Clock.Now,
                                              State,
                                              Status),
                      AuditLog.State     =>+ (AuditLog.FileState,
                                              Clock.Now,
                                              ConfigData.State,
                                              State,
                                              Status),
                      State              =>+ (Input,
                                              Status),
                      Status             =>+ null);

   ------------------------------------------------------------------
   -- UpdateAuthCert
   --
   -- Description:
   --    Updates token with locally stored (Auth Cert) data.
   --    May raise a System Fault.
   --
   -- Traceunit : C.UserToken.UpdateAuthCert
   -- Traceto : FD.Interfac.UpdateToken
   ------------------------------------------------------------------
   procedure UpdateAuthCert (Success : out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 KeyStore.Store,
                                 State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Output,
                                 Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               KeyStore.Store,
                                               State),
                      Output               =>+ (KeyStore.Store,
                                               State,
                                               Status),
                      (Status,
                       Success)            => (KeyStore.Store,
                                               State,
                                               Status));

   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Description:
   --    Returns the user associated with the current token.
   --
   -- Traceunit : C.UserToken.ExtractUser
   -- Traceto : FD.AuditLog.ExtractUser
   ------------------------------------------------------------------
   function ExtractUser return AuditTypes.UserTextT
     with Global => State;

   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Description:
   --    Returns True extactly when the toke is present
   --
   -- Traceunit : C.UserToken.IsPresent
   -- Traceto : FD.RealWorld.State
   ------------------------------------------------------------------
   function IsPresent return Boolean
     with Global => State;

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
   procedure ReadAndCheckAuthCert (AuthCertOK :    out Boolean)
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 Input,
                                 KeyStore.State,
                                 KeyStore.Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State,
                                 Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Input,
                                               KeyStore.Store,
                                               State,
                                               Status),
                      (AuthCertOK,
                       State)              => (Clock.CurrentTime,
                                               Input,
                                               KeyStore.State,
                                               KeyStore.Store,
                                               State,
                                               Status),
                      Status               =>+ State);

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
      TokenOK     :    out Boolean)
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 Input,
                                 KeyStore.Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State,
                                 Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Input,
                                               KeyStore.Store,
                                               State,
                                               Status),
                      (Description,
                       State,
                       TokenOK)            => (Clock.CurrentTime,
                                               Input,
                                               KeyStore.Store,
                                               State,
                                               Status),
                      Status               =>+ State);

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
   procedure AddAuthCert (Success : out Boolean)
     with Global  => (Input  => (CertificateStore.State,
                                 Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 KeyStore.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               CertificateStore.State,
                                               Clock.Now,
                                               ConfigData.State),
                      State                =>+ (CertificateStore.State,
                                                Clock.CurrentTime,
                                                ConfigData.State,
                                                KeyStore.State),
                      Success              => CertificateStore.State),
          Pre     => KeyStore.PrivateKeyPresent;

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
   function GetIandATemplate return IandATypes.TemplateT
     with Global => State;

   ------------------------------------------------------------------
   -- GetClass
   --
   -- Description:
   --    obtains the class value for the Priv certificate.
   --
   -- Traceunit : C.UserToken.GetClass
   -- Traceto : FD.Certificate.NewAuthCert
   ------------------------------------------------------------------
   function GetClass return PrivTypes.ClassT
     with Global => State;

   ------------------------------------------------------------------
   -- Clear
   --
   -- Description:
   --    Clears UserToken.State certificate information
   --
   -- Traceunit : C.UserToken.Clear
   -- Traceto : FD.UserToken.Clear
   ------------------------------------------------------------------
   procedure Clear
     with Global  => (In_Out => State),
          Depends => (State =>+ null);

end UserToken;
