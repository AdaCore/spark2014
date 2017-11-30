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
-- KeyStore.Interfac
--
-- Implementation Notes:
--    Provides the TIS core interface to the crypto library
--
------------------------------------------------------------------
with Crypto;

package body KeyStore.Interfac
  with SPARK_Mode => Off
is

   ------------------------------------------------------------------
   -- GetKeystoreReturn
   --
   -- Description:
   --    Converts the Crypto library return value into the
   --    Keystore return value
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function GetKeystoreReturn (CryptoRet : Crypto.ReturnValueT)
                              return ReturnValueT
   is
     (ReturnValueT'Val(Crypto.ReturnValueT'Pos(CryptoRet)));

   ------------------------------------------------------------------
   -- GetCryptoReturn
   --
   -- Description:
   --    Converts the Keystore return value into the
   --    Crypto library return value
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function GetCryptoReturn (StoreRet : ReturnValueT)
                             return Crypto.ReturnValueT is
     (Crypto.ReturnValueT'Val (ReturnValueT'Pos (StoreRet)));

   ------------------------------------------------------------------
   -- Initialize
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Initialize (ReturnValue : out ReturnValueT) is
      LocalReturnValue : Crypto.ReturnValueT;
   begin
      Crypto.Initialize (ReturnValue => LocalReturnValue);
      ReturnValue := GetKeystoreReturn (LocalReturnValue);
   end Initialize;

   ------------------------------------------------------------------
   -- Finalize
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Finalize (ReturnValue : out ReturnValueT) is
      LocalReturnValue : Crypto.ReturnValueT;
   begin
      Crypto.Finalize(ReturnValue => LocalReturnValue);
      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end Finalize;

   ------------------------------------------------------------------
   -- CreateObject
   --
   -- Implementation Notes:
   --    The object handle isn't required here
   --
   ------------------------------------------------------------------
   procedure CreateObject
     (Template     : in     KeyTemplateT;
      ReturnValue  :    out ReturnValueT)
   is
      LocalTemplate     : Crypto.KeyTemplateT :=
        (AttrMask  => Crypto.MaskT(Template.AttrMask),
         Owner     => Template.Owner,
         KeyID     => Template.KeyID,
         KeyLength => Template.KeyLength,
         IsPublic  => Template.IsPublic,
         Padding   => (others => 0));

      LocalReturnValue   : Crypto.ReturnValueT;
      UnusedObjectHandle : CommonTypes.Unsigned32T;
   begin
      Crypto.CreateObject(Template     => LocalTemplate,
                          ObjectHandle => UnusedObjectHandle,
                          ReturnValue  => LocalReturnValue);
      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end CreateObject;

   ------------------------------------------------------------------
   -- FindObjectsInit
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure FindObjectsInit (Template    : in     KeyTemplateT;
                              ReturnValue :    out ReturnValueT)
   is
      LocalTemplate    : Crypto.KeyTemplateT :=
        (AttrMask  => Crypto.MaskT(Template.AttrMask),
         Owner     => Template.Owner,
         KeyID     => Template.KeyID,
         KeyLength => Template.KeyLength,
         IsPublic  => Template.IsPublic,
         Padding   => (others => 0));
      LocalReturnValue : Crypto.ReturnValueT;
   begin
      Crypto.FindObjectsInit(Template    => LocalTemplate,
                             ReturnValue => LocalReturnValue);
      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end FindObjectsInit;

   ------------------------------------------------------------------
   -- FindObjects
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure FindObjects (HandleCount   : in out CommonTypes.Unsigned32T;
                          ObjectHandles :    out HandleArrayT;
                          ReturnValue   :    out ReturnValueT)
   is
      LocalReturnValue : Crypto.ReturnValueT;
   begin
      Crypto.FindObjects(HandleCount   => HandleCount,
                         ObjectHandles => Crypto.HandleArrayT(ObjectHandles),
                         ReturnValue   => LocalReturnValue);
      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end FindObjects;

   ------------------------------------------------------------------
   -- FindObjectsFinal
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure FindObjectsFinal (ReturnValue : out ReturnValueT)
   is
      LocalReturnValue : Crypto.ReturnValueT;
   begin
      Crypto.FindObjectsFinal(ReturnValue => LocalReturnValue);
      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end FindObjectsFinal;

   ------------------------------------------------------------------
   -- DigestInit
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure DigestInit (Mechanism   : in     CryptoTypes.AlgorithmT;
                         ReturnValue :    out ReturnValueT)
   is
      LocalReturnValue : Crypto.ReturnValueT;
   begin
      Crypto.DigestInit(Mechanism   => Mechanism,
                        ReturnValue => LocalReturnValue);
      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end DigestInit;

   ------------------------------------------------------------------
   -- DigestUpdate
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure DigestUpdate (DataBlock   : in     HundredByteArrayT;
                           ByteCount   : in     CommonTypes.Unsigned32T;
                           ReturnValue :    out ReturnValueT)
   is
      LocalReturnValue : Crypto.ReturnValueT;
   begin
      Crypto.DigestUpdate(DataBlock   => DataBlock,
                          ByteCount   => ByteCount,
                          ReturnValue => LocalReturnValue);
      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end DigestUpdate;

   ------------------------------------------------------------------
   -- DigestFinal
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure DigestFinal (Digest      : out DigestT;
                          ReturnValue : out ReturnValueT)
   is
      LocalDigest      : Crypto.DigestT;
      LocalReturnValue : Crypto.ReturnValueT;
      UnusedLength     : CommonTypes.Unsigned32T;
   begin
      Crypto.DigestFinal(Digest       => LocalDigest,
                         DigestLength => UnusedLength,
                         ReturnValue  => LocalReturnValue);

      Digest := (DigestID     => LocalDigest.DigestID,
                 SignReturn   => GetKeystoreReturn(LocalDigest.SignReturn),
                 VerifyReturn => GetKeystoreReturn(LocalDigest.VerifyReturn),
                 Pad          => (others => 0));

      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end DigestFinal;

   ------------------------------------------------------------------
   -- Sign
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Sign (Mechanism   : in     CryptoTypes.AlgorithmT;
                   KeyHandle   : in     CommonTypes.Unsigned32T;
                   Digest      : in     DigestT;
                   Signature   :    out CertTypes.SignatureT;
                   ReturnValue :    out ReturnValueT)
   is
      LocalDigest      : Crypto.DigestT;
      LocalReturnValue : Crypto.ReturnValueT;
   begin
      LocalDigest := (DigestID     => Digest.DigestID,
                      SignReturn   => GetCryptoReturn(Digest.SignReturn),
                      VerifyReturn => GetCryptoReturn(Digest.VerifyReturn),
                      Pad          => (others => 0));

      Crypto.Sign(Mechanism   => Mechanism,
                  KeyHandle   => KeyHandle,
                  Digest      => LocalDigest,
                  Signature   => Signature,
                  ReturnValue => LocalReturnValue);

      ReturnValue := GetKeyStoreReturn(LocalReturnValue);
   end Sign;

   ------------------------------------------------------------------
   -- Verify
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Verify (Mechanism   : in     CryptoTypes.AlgorithmT;
                     KeyHandle   : in     CommonTypes.Unsigned32T;
                     Digest      : in     DigestT;
                     Signature   : in     CertTypes.SignatureT;
                     ReturnValue :    out ReturnValueT)
   is
      LocalDigest      : Crypto.DigestT;
      LocalReturnValue : Crypto.ReturnValueT;
   begin
      LocalDigest := (DigestID     => Digest.DigestID,
                      SignReturn   => GetCryptoReturn(Digest.SignReturn),
                      VerifyReturn => GetCryptoReturn(Digest.VerifyReturn),
                      Pad          => (others => 0));

      Crypto.Verify(Mechanism   => Mechanism,
                    KeyHandle   => KeyHandle,
                    Digest      => LocalDigest,
                    Signature   => Signature,
                    ReturnValue => LocalReturnValue);
      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end Verify;

   ------------------------------------------------------------------
   -- GetAttributeValue
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure GetAttributeValue (KeyHandle   : in     CommonTypes.Unsigned32T;
                                Template    : in out KeyTemplateT;
                                ReturnValue :    out ReturnValueT)
   is
      LocalTemplate    : Crypto.KeyTemplateT :=
          (AttrMask  => Crypto.MaskT(Template.AttrMask),
           Owner     => Template.Owner,
           KeyID     => Template.KeyID,
           KeyLength => Template.KeyLength,
           IsPublic  => Template.IsPublic,
           Padding   => (others => 0));
      LocalReturnValue : Crypto.ReturnValueT;
   begin
      Crypto.GetAttributeValue(KeyHandle   => KeyHandle,
                               Template    => LocalTemplate,
                               ReturnValue => LocalReturnValue);

      Template := KeyTemplateT'(AttrMask  => MaskT(LocalTemplate.AttrMask),
                                Owner     => LocalTemplate.Owner,
                                KeyID     => LocalTemplate.KeyID,
                                KeyLength => LocalTemplate.KeyLength,
                                IsPublic  => LocalTemplate.IsPublic);

      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end GetAttributeValue;

   ------------------------------------------------------------------
   -- Delete
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Delete is
   begin
      Crypto.ClearStore;
   end Delete;

end KeyStore.Interfac;
