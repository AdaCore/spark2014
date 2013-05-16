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
-- KeyStore.Interface
--
-- Description:
--    Thin layer for the crypto library
--
------------------------------------------------------------------
with BasicTypes,
     CertTypes,
     CryptoTypes;

--# inherit BasicTypes,
--#         CertTypes,
--#         CryptoTypes;

private package KeyStore.Interface
--# own Store;
--# initializes Store;
is

   -- As this library will only be storing key objects we are only
   -- interested in Key templates. Key data in this system is
   -- replaced by dummy keys, consisting of an Owner, a Key ID, a
   -- KeyLength, and a Boolean flag indicating whether the key is
   -- public or private. KeyTemplateT includes these as attributes,
   -- and a mask to determine which of the attributes are defined.

   -- Each attribute will have a corresponding bit in AttrMask, which
   -- will be set if the attribute is defined:

   type MaskT is mod 16;
   for MaskT'Size use 32;

   OwnerMask     : constant maskT := 1;
   KeyIDMask     : constant MaskT := 2;
   KeyLengthMask : constant MaskT := 4;
   IsPublicMask  : constant MaskT := 8;

   FullKeyMask : constant MaskT := (OwnerMask + KeyIDMask) +
                                   (KeyLengthMask + IsPublicMask);

   type KeyTemplateT is record
      AttrMask  : MaskT;
      Owner     : CryptoTypes.IssuerT;
      KeyID     : BasicTypes.Unsigned32T;
      KeyLength : BasicTypes.Unsigned32T;
      IsPublic  : Boolean;
   end record;

   subtype HundredByteIndexT is Integer range 1..100;
   subtype HundredByteArrayT is String(HundredByteIndexT);

   type HandleCountT is range 0..20;
   subtype HandleArrayI is HandleCountT range 1..HandleCountT'Last;
   type HandleArrayT is array(HandleArrayI) of BasicTypes.Unsigned32T;

   type ReturnValueT is (
      Ok,
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
      CryptokiAlreadyInitialized
      );

   -- DigestT represents the digest information contained in a
   -- certificate. Padded for realistic size.
   type DigestPadI is range 1..20;
   type DigestPadT is array (DigestPadI) of BasicTypes.ByteT;

   type DigestT is record
      DigestID     : BasicTypes.Unsigned32T;
      SignReturn   : ReturnValueT;
      VerifyReturn : ReturnValueT;
      Pad          : DigestPadT;
   end record;

   NullDigest : constant DigestT :=
                            DigestT'(
                               DigestID     => BasicTypes.Unsigned32T'First,
                               SignReturn   => FunctionFailed,
                               VerifyReturn => FunctionFailed,
                               Pad          => DigestPadT'(others => 0));



   ------------------------------------------------------------------
   -- Initialize
   --
   -- Description:
   --    Used to initialize the crypto library at TIS startup.
   --
   ------------------------------------------------------------------
   procedure Initialize(ReturnValue : out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue from Store;


   ------------------------------------------------------------------
   -- Finalize
   --
   -- Description:
   --    Used to finalize the crypto library.
   --
   ------------------------------------------------------------------
   procedure Finalize(ReturnValue : out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue from Store;


   ------------------------------------------------------------------
   -- CreateObject
   --
   -- Description:
   --    Can be used to store keys in the crypto database.
   --
   ------------------------------------------------------------------

   procedure CreateObject(Template     : in     KeyTemplateT;
                          ReturnValue  :    out ReturnValueT);
   --# global in out Store;
   --# derives Store,
   --#         ReturnValue from Store,
   --#                          Template;

   ------------------------------------------------------------------
   -- FindObjectsInit
   --
   -- Description:
   --    The FindObjects set of procedures are used to search the crypto
   --    library for an object matching a given template, obtained here.
   --
   ------------------------------------------------------------------

   procedure FindObjectsInit(Template    : in     KeyTemplateT;
                             ReturnValue :    out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue from Store,
   --#                          Template;


   ------------------------------------------------------------------
   -- FindObjects
   --
   -- Description:
   --    Called after FindObjectsInit, and continues the search, returning
   --    found matches.
   --
   ------------------------------------------------------------------

   procedure FindObjects(HandleCount   : in out BasicTypes.Unsigned32T;
                         ObjectHandles :    out HandleArrayT;
                         ReturnValue   :    out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue,
   --#         ObjectHandles,
   --#         HandleCount   from Store,
   --#                            HandleCount;

   ------------------------------------------------------------------
   -- FindObjectsFinal
   --
   -- Description:
   --    Finalizes the find operation.
   --
   ------------------------------------------------------------------

   procedure FindObjectsFinal(ReturnValue : out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue from Store;

   ------------------------------------------------------------------
   -- DigestInit
   --
   -- Description:
   --    The Digest operations are used when verifying signed certificates, and
   --    when the system is signing an authorization certificate.
   --    DigestInit initializes the operation, and obtains a mechanism, from
   --    which TIS can determine the type of digest to produce.
   --
   ------------------------------------------------------------------

   procedure DigestInit(Mechanism   : in     CryptoTypes.AlgorithmT;
                        ReturnValue :    out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue from Store,
   --#                          Mechanism;


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

   procedure DigestUpdate(DataBlock   : in     HundredByteArrayT;
                          ByteCount   : in     BasicTypes.Unsigned32T;
                          ReturnValue :    out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue from Store,
   --#                          DataBlock,
   --#                          ByteCount;

   ------------------------------------------------------------------
   -- DigestFinal
   --
   -- Description:
   --    Called after all of the certificate has been read and finalizes the
   --    digest operation, returning the produced digest.
   --
   ------------------------------------------------------------------

   procedure DigestFinal(Digest       : out DigestT;
                         ReturnValue  : out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue,
   --#         Digest      from Store;

   ------------------------------------------------------------------
   -- Sign
   --
   -- Description:
   --    Signs the TIS created Auth Cert.
   --
   ------------------------------------------------------------------

   procedure Sign(Mechanism    : in     CryptoTypes.AlgorithmT;
                  KeyHandle    : in     BasicTypes.Unsigned32T;
                  Digest       : in     DigestT;
                  Signature    :    out CertTypes.SignatureT;
                  ReturnValue  :    out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue,
   --#         Signature   from Store,
   --#                          Mechanism,
   --#                          Digest,
   --#                          KeyHandle;

   ------------------------------------------------------------------
   -- Verify
   --
   -- Description:
   --    Performs the verification of the signature appended to a certificate
   --    against the digest of the certificate.
   --
   ------------------------------------------------------------------

   procedure Verify(Mechanism    : in     CryptoTypes.AlgorithmT;
                    KeyHandle    : in     BasicTypes.Unsigned32T;
                    Digest       : in     DigestT;
                    Signature    : in     CertTypes.SignatureT;
                    ReturnValue  :    out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue from Store,
   --#                          Mechanism,
   --#                          Digest,
   --#                          Signature,
   --#                          KeyHandle;

   ------------------------------------------------------------------
   -- GetAttributeValue
   --
   -- Description:
   --    Extracts attribute data from the object pointed to by KeyHandle.
   --
   ------------------------------------------------------------------

   procedure GetAttributeValue(KeyHandle   : in     BasicTypes.Unsigned32T;
                               Template    : in out KeyTemplateT;
                               ReturnValue :    out ReturnValueT);
   --# global in Store;
   --# derives ReturnValue,
   --#         Template    from Store,
   --#                          Template,
   --#                          KeyHandle;


   ------------------------------------------------------------------
   -- Delete
   --
   -- Description:
   --    Deletes the KeyStore.
   --
   ------------------------------------------------------------------

   procedure Delete;
   --# global in out Store;
   --# derives Store from *;

end KeyStore.Interface;
