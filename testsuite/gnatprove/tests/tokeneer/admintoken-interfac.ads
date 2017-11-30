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
-- AdminToken.Interfac
--
-- Description:
--    Provides access to the User Token via the Token Reader interface.
--
------------------------------------------------------------------

with CommonTypes,
     CertTypes,
     TokenTypes;

private package AdminToken.Interfac
  with Abstract_State => ((State  with Part_Of  => AdminToken.State),
                          (Status with Part_Of  => AdminToken.Status),
                          (Input  with External => Async_Writers,
                                       Part_Of  => AdminToken.Input)),
       Initializes    => Status
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
   procedure Init
     with Global  => (Output => State,
                      In_Out => Status),
          Depends => ((State,
                       Status) => Status);

   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Polls the admin token reader to update the recorded state
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
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               State,
                                               Status),
                      State                =>+ (Input,
                                                Status),
                      Status               =>+ null);

   ------------------------------------------------------------------
   -- TheTokenPresence
   --
   -- Description:
   --    Returns whether an admin token is present.
   --
   ------------------------------------------------------------------
   function TheTokenPresence return CommonTypes.PresenceT
     with Global => State;

   ------------------------------------------------------------------
   -- TheTokenID
   --
   -- Description:
   --    Returns the token ID of a present admin token.
   --
   ------------------------------------------------------------------
   function TheTokenID return TokenTypes.TokenIDT
     with Global => State;

   ------------------------------------------------------------------
   -- TheTokenTry
   --
   -- Description:
   --    Returns return whether the admin token is not present,
   --    bad or good.
   --
   ------------------------------------------------------------------
   function TheTokenTry return TokenTypes.TryT
     with Global => State;

   ------------------------------------------------------------------
   -- GetCertificate
   --
   -- Description:
   --    Gets the specified certificate from the user token.If the token is
   --    found successfully then Found is set true.Any problems obtaining the
   --    certificate will cause Found to be set false.
   --
   ------------------------------------------------------------------
   procedure GetCertificate
     (CertType  : in     CertTypes.CertificateT;
      RawCert   :    out CertTypes.RawCertificateT;
      Found     :    out Boolean)
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

end AdminToken.Interfac;
