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
-- TokenReader
--
-- Description:
--    Package maintaining and controlling the token readers.
--
------------------------------------------------------------------
with AuditLog;
with CommonTypes;
with CertTypes;
with Clock;
with ConfigData;
with TokenTypes;


package TokenReader
  with SPARK_Mode,
       Abstract_State => (State,
                          (Status with External => Async_Writers),
                          (Input  with External => Async_Writers),
                          (Output with External => Async_Readers)),
       Initializes    => Status
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

   procedure Init
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Status),
                      Output => State,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Status),
                      State                => Status);

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

   procedure Poll (Reader : in ReaderT)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Input,
                                 Status),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Reader,
                                               State,
                                               Status),
                      State                =>+ (Input,
                                                Reader,
                                                Status));

   ------------------------------------------------------------------
   -- TheTokenPresence
   --
   -- Description:
   --    Returns whether a token is present.
   --
   -- traceunit : C.TokenReader.TheTokenPresence
   ------------------------------------------------------------------
   function TheTokenPresence (Reader : ReaderT) return CommonTypes.PresenceT
     with Global => State;

   ------------------------------------------------------------------
   -- TheTokenID
   --
   -- Description:
   --    Returns the token ID of a present token.
   --
   -- traceunit : C.TokenReader.TheTokenID
   ------------------------------------------------------------------
   function TheTokenID (Reader : ReaderT) return TokenTypes.TokenIDT
     with Global => State;

   ------------------------------------------------------------------
   -- TheTokenTry
   --
   -- Description:
   --    Returns return whether the token is not present, bad or good.
   --
   -- traceunit : C.TokenReader.TheTokenTry
   ------------------------------------------------------------------
   function TheTokenTry (Reader : ReaderT) return TokenTypes.TryT
     with Global => State;

   ------------------------------------------------------------------
   -- GetCertificate
   --
   -- Description:
   --    Gets the specified certificate from the token.If the token is
   --    found successfully then Found is set true.Any problems obtaining the
   --    certificate will cause Found to be set false.
   --
   -- traceunit : C.TokenReader.GetCertificate
   ------------------------------------------------------------------
   procedure GetCertificate (Reader   : in     ReaderT;
                             CertType : in     CertTypes.CertificateT;
                             RawCert  :    out CertTypes.RawCertificateT;
                             Found    :    out Boolean)
     with Global  => (Input  => (Input,
                                 State,
                                 Status)),
          Depends => (Found   => (CertType,
                                  Reader,
                                  State,
                                  Status),
                      RawCert => (CertType,
                                  Input,
                                  Reader,
                                  State,
                                  Status));

   ------------------------------------------------------------------
   -- WriteAuthCertificate
   --
   -- Description:
   --    Writes the auth cert to the user token.If there are any problems
   --    then success is set to false.
   --
   -- traceunit : C.TokenReader.GetCertificate
   ------------------------------------------------------------------
   procedure WriteAuthCertificate
     (RawCert : in     CertTypes.RawCertificateT;
      Success :    out Boolean)
     with Global  => (Input  => (State,
                                 Status),
                      Output => Output),
          Depends => (Output  => (RawCert,
                                  State,
                                  Status),
                      Success => (State,
                                  Status));

end TokenReader;
