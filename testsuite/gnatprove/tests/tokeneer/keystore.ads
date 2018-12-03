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
-- KeyStore
--
-- Description:
--    Provides the TIS core interface to the crypto library
--
------------------------------------------------------------------

with CommonTypes,
     CertTypes,
     Clock,
     ConfigData,
     CryptoTypes,
     Auditlog;

use type CryptoTypes.IssuerT;

package KeyStore
  with Abstract_State => (State,
                          Store),
       Initializes    => Store
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes the crypto library.May raise a system fault
   --
   -- Traceunit : C.KeyStore.Init
   -- Traceto   : FD.TIS.TISStartup
   ------------------------------------------------------------------
   procedure Init
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Store),
                      Output => State,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Store),
                      State                => Store);

   ------------------------------------------------------------------
   -- KeyMatchingIssuerPresent
   --
   -- Description:
   --    Searches the key store for a key owned by the imported issuer ID.
   --    Returns a flag stating whether keyMatchingIssuer is null.
   --    May raise a system fault.
   --
   -- Traceunit : C.KeyStore.KeyMatchingIssuerPresent
   -- Traceto   : FD.Certificate.SignedOK
   --             FD.KeyStore.State
   ------------------------------------------------------------------
   procedure KeyMatchingIssuerPresent (Issuer    : in     CryptoTypes.IssuerT;
                                       IsPresent :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Issuer,
                                               Store),
                      IsPresent            => (Issuer,
                                               Store));

   ------------------------------------------------------------------
   -- PrivateKeyPresent
   --
   -- Description:
   --    Searches the key store for the TIS's private key.
   --    Returns a flag equivalent to the Z statement privateKey /= nil
   --
   -- Traceunit : C.KeyStore.PrivateKeyPresent
   -- Traceto   : FD.Certificate.AuthCertSignedOk
   ------------------------------------------------------------------
   function PrivateKeyPresent return Boolean
     with Global => State;

   ------------------------------------------------------------------
   -- IssuerIsThisTIS
   --
   -- Description:
   --    Determines whether the given issuer is this TIS.
   --
   -- Traceunit : C.KeyStore.IssuerIsThisTIS
   -- Traceto   : FD.Certificate.AuthCertSignedOk
   ------------------------------------------------------------------
   function IssuerIsThisTIS (Issuer : CryptoTypes.IssuerT) return Boolean
     with Global => State;

   ------------------------------------------------------------------
   -- ThisTIS
   --
   -- Description:
   --    Given a Key handle, returns the name of this TIS
   --
   -- Traceunit : C.KeyStore.ThisTIS
   -- Traceto   : FD.KeyStore.State
   ------------------------------------------------------------------
   function ThisTIS return CryptoTypes.IssuerT
     with Global => State;

   ------------------------------------------------------------------
   -- IsVerifiedBy
   --
   -- Description:
   --    Attempts to verify the certificate.May raise a system fault.
   --
   -- Traceunit : C.KeyStore.IsVerifiedBy
   -- Traceto   : FD.KeyTypes.Keys
   ------------------------------------------------------------------
   procedure IsVerifiedBy (Mechanism   : in     CryptoTypes.AlgorithmT;
                           RawCertData : in     CertTypes.RawDataT;
                           Signature   : in     CertTypes.SignatureT;
                           TheIssuer   : in     CryptoTypes.IssuerT;
                           Verified    :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Mechanism,
                                               RawCertData,
                                               Signature,
                                               Store,
                                               TheIssuer),
                      Verified             => (Mechanism,
                                               RawCertData,
                                               Signature,
                                               Store,
                                               TheIssuer));

   ------------------------------------------------------------------
   -- Sign
   --
   -- Description:
   --    Attempts to sign the certificate.May raise a system fault.
   --
   -- Traceunit : C.KeyStore.Sign
   -- Traceto   : FD.KeyTypes.Keys
   ------------------------------------------------------------------
   procedure Sign (RawCertData : in     CertTypes.RawDataT;
                   Signature   :    out CertTypes.SignatureT;
                   Signed      :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               RawCertData,
                                               Store),
                      (Signature,
                       Signed)             => (RawCertData,
                                               Store));

   ------------------------------------------------------------------
   -- AddKey
   --
   -- Description:
   --    Adds a key to the Keystore
   --
   -- Traceunit : C.KeyStore.AddKey
   -- Traceto   : FD.KeyTypes.UpdateKeyStore
   ------------------------------------------------------------------
   procedure AddKey (TheOwner : in     CryptoTypes.IssuerT;
                     TheKey   : in     CryptoTypes.KeyPartT;
                     IsPublic : in     Boolean;
                     Added    :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State,
                                 Store)),
          Depends => ((Added,
                       Store)              => (IsPublic,
                                               Store,
                                               TheKey,
                                               TheOwner),
                      (AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               IsPublic,
                                               Store,
                                               TheKey,
                                               TheOwner),
                      State                =>+ (IsPublic,
                                                Store,
                                                TheKey,
                                                TheOwner)),
          Post    => (Added and (not IsPublic) and PrivateKeyPresent)
                       xor (not (Added and not IsPublic)
                              and (PrivateKeyPresent = PrivateKeyPresent'Old));

   ------------------------------------------------------------------
   -- Delete
   --
   -- Description:
   --    Deletes the KeyStore file.
   --
   -- Traceunit : C.KeyStore.AddKey
   -- Traceto   : FD.KeyTypes.UpdateKeyStore
   ------------------------------------------------------------------
   procedure Delete
     with Global  => (Output => State,
                      In_Out => Store),
          Depends => (State =>  null,
                      Store =>+ null),
          Post    => not PrivateKeyPresent;

private
   ----------------------------------------------------------------
   -- Types
   ----------------------------------------------------------------
   type OptionalPrivateKeyT is record
      IsPresent : Boolean;
      Owner     : CryptoTypes.IssuerT;
   end record;

   ----------------------------------------------------------------
   -- State
   ----------------------------------------------------------------

   ThisTISInfo : OptionalPrivateKeyT with Part_Of => State;


   -- Key handles are unsigned 32 bit words, with zero being a null
   -- key handle.
   NullKey : constant CommonTypes.Unsigned32T := 0;

   ------------------------------------------------------------------
   -- PrivateKeyPresent
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function PrivateKeyPresent return Boolean is (ThisTISInfo.IsPresent)
     with Refined_Global  => ThisTISInfo;

   ------------------------------------------------------------------
   -- IssuerIsThisTIS
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function IssuerIsThisTIS (Issuer : in     CryptoTypes.IssuerT)
                            return Boolean
   is
     (if PrivateKeyPresent then
         Issuer = ThisTISInfo.Owner
      else
         False)
     with Refined_Global => ThisTISInfo;

   ------------------------------------------------------------------
   -- ThisTIS
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function ThisTIS return CryptoTypes.IssuerT is (ThisTISInfo.Owner)
     with Refined_Global => ThisTISInfo;

end KeyStore;
