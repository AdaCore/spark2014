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
-- KeyStore
--
-- Description:
--    Provides the TIS core interface to the crypto library
--
------------------------------------------------------------------

with BasicTypes,
     CertTypes,
     CryptoTypes;
--# inherit AuditLog,
--#         AuditTypes,
--#         BasicTypes,
--#         CertTypes,
--#         Clock,
--#         ConfigData,
--#         CryptoTypes;

package KeyStore
--# own State;
--#     Store : Prf_StoreT;
--# initializes Store;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes the crypto library. May raise a system fault
   --
   -- Traceunit : C.KeyStore.Init
   -- Traceto   : FD.TIS.TISStartup
   ------------------------------------------------------------------
   procedure Init;
   --# global in     Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out State;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Store,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         State              from Store;


   -- A proof function for use as a precondition for Verify
   --# type Prf_StoreT is abstract;

   --# function Prf_IssuerKeyNotNull(Issuer : CryptoTypes.IssuerT;
   --#                               Store  : Prf_StoreT)
   --#          return Boolean;

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
   procedure KeyMatchingIssuerPresent(Issuer    : in     CryptoTypes.IssuerT;
                                      IsPresent :    out Boolean);
   --# global in     Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Store,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Issuer &
   --#         IsPresent          from Store,
   --#                                 Issuer;
   --# post IsPresent <-> Prf_IssuerKeyNotNull(Issuer, Store);



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
   function PrivateKeyPresent return Boolean;
   --# global State;


   ------------------------------------------------------------------
   -- IssuerIsThisTIS
   --
   -- Description:
   --    Determines whether the given issuer is this TIS.
   --
   -- Traceunit : C.KeyStore.IssuerIsThisTIS
   -- Traceto   : FD.Certificate.AuthCertSignedOk
   ------------------------------------------------------------------
   function IssuerIsThisTIS(Issuer : CryptoTypes.IssuerT)
     return Boolean ;
   --# global State;


   ------------------------------------------------------------------
   -- ThisTIS
   --
   -- Description:
   --    Given a Key handle, returns the name of this TIS
   --
   -- Traceunit : C.KeyStore.ThisTIS
   -- Traceto   : FD.KeyStore.State
   ------------------------------------------------------------------
   function ThisTIS return CryptoTypes.IssuerT;
   --# global State;



   ------------------------------------------------------------------
   -- IsVerifiedBy
   --
   -- Description:
   --    Attempts to verify the certificate. May raise a system fault.
   --
   -- Traceunit : C.KeyStore.IsVerifiedBy
   -- Traceto   : FD.KeyTypes.Keys
   ------------------------------------------------------------------
   procedure  IsVerifiedBy(Mechanism   : in     CryptoTypes.AlgorithmT;
                           RawCertData : in     CertTypes.RawDataT;
                           Signature   : in     CertTypes.SignatureT;
                           TheIssuer   : in     CryptoTypes.IssuerT;
                           Verified    :    out Boolean);
   --# global in     Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Store,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 TheIssuer,
   --#                                 Mechanism,
   --#                                 RawCertData,
   --#                                 Signature &
   --#         Verified           from Store,
   --#                                 TheIssuer,
   --#                                 Mechanism,
   --#                                 RawCertData,
   --#                                 Signature;
   --# pre Prf_IssuerKeyNotNull(TheIssuer, Store);


   ------------------------------------------------------------------
   -- Sign
   --
   -- Description:
   --    Attempts to sign the certificate. May raise a system fault.
   --
   -- Traceunit : C.KeyStore.Sign
   -- Traceto   : FD.KeyTypes.Keys
   ------------------------------------------------------------------
   procedure  Sign(RawCertData : in     CertTypes.RawDataT;
                   Signature   :    out CertTypes.SignatureT;
                   Signed      :    out Boolean);
   --# global in     Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Store,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 RawCertData &
   --#         Signature,
   --#         Signed             from Store,
   --#                                 RawCertData;


   ------------------------------------------------------------------
   -- AddKey
   --
   -- Description:
   --    Adds a key to the Keystore
   --
   -- Traceunit : C.KeyStore.AddKey
   -- Traceto   : FD.KeyTypes.UpdateKeyStore
   ------------------------------------------------------------------
   procedure AddKey(TheOwner : in     CryptoTypes.IssuerT;
                    TheKey   : in     CryptoTypes.KeyPartT;
                    IsPublic : in     Boolean;
                    Added    :    out Boolean);
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out Store;
   --# derives State,
   --#         Store              from *,
   --#                                 Store,
   --#                                 TheOwner,
   --#                                 TheKey,
   --#                                 IsPublic &
   --#         AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Store,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 TheOwner,
   --#                                 TheKey,
   --#                                 IsPublic &
   --#         Added              from Store,
   --#                                 TheOwner,
   --#                                 TheKey,
   --#                                 IsPublic;
   --# post ((Added and not IsPublic) -> PrivateKeyPresent(State)) and
   --#      (not (Added and not IsPublic) -> PrivateKeyPresent(State) =
   --#                                        PrivateKeyPresent(State~));


   ------------------------------------------------------------------
   -- Delete
   --
   -- Description:
   --    Deletes the KeyStore file.
   --
   -- Traceunit : C.KeyStore.AddKey
   -- Traceto   : FD.KeyTypes.UpdateKeyStore
   ------------------------------------------------------------------
   procedure Delete;
   --# global in out Store;
   --#           out State;
   --# derives State from  &
   --#         Store from *;
   --# post not PrivateKeyPresent(State);



end KeyStore;
