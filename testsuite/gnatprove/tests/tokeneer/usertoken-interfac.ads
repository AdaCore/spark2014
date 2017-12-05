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
-- UserToken.Interfac
--
-- Description:
--    Provides access to the User Token via the Token Reader interface.
--
------------------------------------------------------------------

with AuditLog,
     CommonTypes,
     CertTypes,
     Clock,
     ConfigData,
     TokenTypes;

private package UserToken.Interfac
  with Abstract_State => ((State  with Part_Of  => UserToken.State),
                          (Status with Part_Of  => UserToken.Status),
                          (Input  with External => Async_Writers,
                                       Part_Of  => UserToken.Input),
                          (Output with External => Async_Readers,
                                       Part_Of  => UserToken.Output)),
       Initializes    => (Status, Output)
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
   --    Polls the user token reader to update the recorded state
   --    of the reader - determines whether a token is present.
   --
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
   -- TheTokenPresence
   --
   -- Description:
   --    Returns whether a user token is present.
   --
   ------------------------------------------------------------------
   function TheTokenPresence return CommonTypes.PresenceT
     with Global => State;

   ------------------------------------------------------------------
   -- TheTokenID
   --
   -- Description:
   --    Returns the token ID of a present token.
   --
   ------------------------------------------------------------------
   function TheTokenID return TokenTypes.TokenIDT
     with Global => State;

   ------------------------------------------------------------------
   -- TheTokenTry
   --
   -- Description:
   --    Returns return whether the token is not present, bad or good.
   --
   ------------------------------------------------------------------
   function TheTokenTry return TokenTypes.TryT
     with Global => State;

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
     (CertType : in     CertTypes.CertificateT;
      RawCert  :    out CertTypes.RawCertificateT;
      Found    :    out Boolean)
     with Global  => (Input  => (Input,
                                 State),
                      In_Out => Status),
          Depends => (Found   => (CertType,
                                  State,
                                  Status),
                      RawCert => (CertType,
                                  Input,
                                  State,
                                  Status),
                      Status  =>+ null);

   ------------------------------------------------------------------
   -- WriteAuthCertificate
   --
   -- Description:
   --    Writes the auth cert to the user token. If there are any problems
   --    then success is set to false.
   --
   ------------------------------------------------------------------
   procedure WriteAuthCertificate
     (RawCert : in     CertTypes.RawCertificateT;
      Success :    out Boolean)
     with Global  => (Input  => State,
                      Output => Output,
                      In_Out => Status),
          Depends => (Output  => (RawCert,
                                  State,
                                  Status),
                      Status  =>+ null,
                      Success => (State,
                                  Status));

end UserToken.Interfac;
