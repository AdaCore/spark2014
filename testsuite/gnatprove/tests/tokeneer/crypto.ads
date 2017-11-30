
------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- Crypto
--
-- Description:
--    Stub representation of a Crypto library, provides a means of storing
--    Keys, and performing crypto operations.
--    The procedures used are based very closely on those given in the Cryptoki
--    interface.
--
------------------------------------------------------------------

with CommonTypes,
     CertTypes,
     CryptoTypes,
     SPARK_IO;

package Crypto is

   -- As this library will only be storing key objects we are only
   -- interested in Key templates. Key data in this system is
   -- replaced by dummy keys, consisting of an Owner, a Key ID, a
   -- KeyLength, and a Boolean flag indicating whether the key is
   -- public or private. KeyTemplateT includes these as attributes,
   -- and a mask to determine which of the attributes are defined
   -- Padding is included to retain a
   -- sensible size (128 bytes).

   subtype KeyPaddingIndexT is Integer range 1..67;
   type KeyPaddingT is array(KeyPaddingIndexT) of CommonTypes.ByteT;

   -- Each attribute will have a corresponding bit in AttrMask, which
   -- will be set if the attribute is defined:

   type MaskT is mod 16;
   for MaskT'Size use 32;

   OwnerMask     : constant maskT := 1;
   KeyIDMask     : constant MaskT := 2;
   KeyLengthMask : constant MaskT := 4;
   IsPublicMask  : constant MaskT := 8;

   type KeyTemplateT is record
      AttrMask  : MaskT;                   -- 4 bytes
      Owner     : CryptoTypes.IssuerT;     -- 48 bytes
      KeyID     : CommonTypes.Unsigned32T;  -- 4 bytes
      KeyLength : CommonTypes.Unsigned32T;  -- 4 bytes
      IsPublic  : Boolean;                 -- 1 byte
      Padding   : KeyPaddingT;             -- 128 - 61 = 67 bytes
   end record;

   subtype HundredByteIndexT is Integer range 1..100;
   subtype HundredByteArrayT is String(HundredByteIndexT);

   type HandleCountT is range 0..20;
   subtype HandleArrayI is HandleCountT range 1..HandleCountT'Last;
   type HandleArrayT is array(HandleArrayI) of CommonTypes.Unsigned32T;

   type ReturnValueT is
     (Ok,
      HostMemory,
      GeneralError,
      FunctionFailed,
      ArgumentsBad,
      AttributeReadOnly,
      AttributeTypeInvalid,
      AttributeValueInvalid,
      DataInvalid,
      DataLenRange,
      DeviceError,
      DeviceMemory,
      FunctionCanceled,
      KeyHandleInvalid,
      KeySizeRange,
      KeyTypeInconsistent,
      KeyFunctionNotPermitted,
      MechanismInvalid,
      MechanismParamInvalid,
      ObjectHandleInvalid,
      OperationActive,
      OperationNotInitialized,
      SignatureInvalid,
      SignatureLenRange,
      TemplateIncomplete,
      TemplateInconsistent,
      BufferTooSmall,
      CryptokiNotInitialized,
      CryptokiAlreadyInitialized);

   -- DigestT represents the digest information contained in a
   -- certificate. Padded for realistic size.
   type DigestPadI is range 1..20;
   type DigestPadT is array (DigestPadI) of CommonTypes.ByteT;

   type DigestT is record
      DigestID     : CommonTypes.Unsigned32T;
      SignReturn   : ReturnValueT;
      VerifyReturn : ReturnValueT;
      Pad          : DigestPadT;
   end record;


   ------------------------------------------------------------------
   -- Initialize
   --
   -- Description:
   --    Used to initialize the crypto library at TIS startup.
   --
   ------------------------------------------------------------------
   procedure Initialize (ReturnValue : out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- Finalize
   --
   -- Description:
   --    Used to finalize the crypto library.
   --
   ------------------------------------------------------------------
   procedure Finalize (ReturnValue : out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- CreateObject
   --
   -- Description:
   --    Can be used to store keys in the crypto database.
   --
   ------------------------------------------------------------------
   procedure CreateObject (Template     : in     KeyTemplateT;
                           ObjectHandle :    out CommonTypes.Unsigned32T;
                           ReturnValue  :    out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- FindObjectsInit
   --
   -- Description:
   --    The FindObjects set of procedures are used to search the crypto
   --    library for an object matching a given template, obtained here.
   --
   ------------------------------------------------------------------
   procedure FindObjectsInit (Template    : in     KeyTemplateT;
                              ReturnValue :    out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- FindObjects
   --
   -- Description:
   --    Called after FindObjectsInit, and continues the search, returning
   --    found matches.
   --
   ------------------------------------------------------------------
   procedure FindObjects (HandleCount   : in out CommonTypes.Unsigned32T;
                          ObjectHandles :    out HandleArrayT;
                          ReturnValue   :    out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- FindObjectsFinal
   --
   -- Description:
   --    Finalizes the find operation.
   --
   ------------------------------------------------------------------
   procedure FindObjectsFinal (ReturnValue : out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- DigestInit
   --
   -- Description:
   --    The Digest operation are used when verifying signed certificates, and
   --    when the system is signing an authorization certificate.
   --    DigestInit initializes the operation, and obtains a mechanism, from
   --    which TIS can determine the type of digest to produce.
   --
   ------------------------------------------------------------------
   procedure DigestInit (Mechanism   : in     CryptoTypes.AlgorithmT;
                         ReturnValue :    out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- DigestUpdate
   --
   -- Description:
   --    Called a number of times to read all of the raw certificate data,
   --    in 100 byte chunks. The whole of the certificate must be read in to
   --    ensure that the CryptoControl field is visible.
   --    Performs the digest.
   --
   ------------------------------------------------------------------
   procedure DigestUpdate (DataBlock   : in     HundredByteArrayT;
                           ByteCount   : in     CommonTypes.Unsigned32T;
                           ReturnValue :    out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- DigestFinal
   --
   -- Description:
   --    Called after all of the certificate has been read and finalizes the
   --    digest operation, returning the produced digest.
   --
   ------------------------------------------------------------------
   procedure DigestFinal (Digest       : out DigestT;
                          DigestLength : out CommonTypes.Unsigned32T;
                          ReturnValue  : out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- Sign
   --
   -- Description:
   --    Signs the TIS created Auth Cert.
   --
   ------------------------------------------------------------------
   procedure Sign (Mechanism    : in     CryptoTypes.AlgorithmT;
                   KeyHandle    : in     CommonTypes.Unsigned32T;
                   Digest       : in     DigestT;
                   Signature    :    out CertTypes.SignatureT;
                   ReturnValue  :    out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- Verify
   --
   -- Description:
   --    Performs the verification of the signature appended to a certificate
   --    against the digest of the certificate.
   --
   ------------------------------------------------------------------
   procedure Verify (Mechanism    : in     CryptoTypes.AlgorithmT;
                     KeyHandle    : in     CommonTypes.Unsigned32T;
                     Digest       : in     DigestT;
                     Signature    : in     CertTypes.SignatureT;
                     ReturnValue  :    out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- GetAttributeValue
   --
   -- Description:
   --    Extracts attribute data from the object pointed to by KeyHandle.
   --
   ------------------------------------------------------------------
   procedure GetAttributeValue (KeyHandle   : in     CommonTypes.Unsigned32T;
                                Template    : in out KeyTemplateT;
                                ReturnValue :    out Crypto.ReturnValueT);

   ------------------------------------------------------------------
   -- ClearStore
   --
   -- Description:
   --    Clears all data from the keystore file
   --
   ------------------------------------------------------------------
   procedure ClearStore;

end Crypto;
