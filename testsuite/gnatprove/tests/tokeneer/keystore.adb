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
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------

with AuditLog,
     AuditTypes,
     CommonTypes,
     CryptoTypes,
     DisplayAPI,
     KeyStore.Interfac;

use type CommonTypes.Unsigned32T;
use type KeyStore.Interfac.ReturnValueT;
use type KeyStore.Interfac.MaskT;

package body KeyStore
  with Refined_State => (Store => KeyStore.Interfac.Store,
                         State => ThisTISInfo)
is
   ----------------------------------------------------------------
   -- Types
   ----------------------------------------------------------------
   type IsSystemT is array (Interfac.ReturnValueT) of Boolean;

   ----------------------------------------------------------------
   -- State
   ----------------------------------------------------------------
   -- Crypto errors can be groupes as a System Error, or a User Error.
   IsSystem : constant IsSystemT := IsSystemT'
     (Interfac.Ok                         => False,
      Interfac.HostMemory                 => True,
      Interfac.GeneralError               => True,
      Interfac.FunctionFailed             => True,
      Interfac.ArgumentsBad               => False,
      Interfac.AttributeReadOnly          => False,
      Interfac.AttributeTypeInvalid       => False,
      Interfac.AttributeValueInvalid      => False,
      Interfac.DataInvalid                => False,
      Interfac.DataLenRange               => False,
      Interfac.DeviceError                => True,
      Interfac.DeviceMemory               => True,
      Interfac.FunctionCanceled           => True,
      Interfac.KeyHandleInvalid           => False,
      Interfac.KeySizeRange               => False,
      Interfac.KeyTypeInconsistent        => False,
      Interfac.KeyFunctionNotPermitted    => False,
      Interfac.MechanismInvalid           => False,
      Interfac.MechanismParamInvalid      => False,
      Interfac.ObjectHandleInvalid        => False,
      Interfac.OperationActive            => True,
      Interfac.OperationNotInitialized    => True,
      Interfac.SignatureInvalid           => False,
      Interfac.SignatureLenRange          => False,
      Interfac.TemplateIncomplete         => False,
      Interfac.TemplateInconsistent       => False,
      Interfac.BufferTooSmall             => True,
      Interfac.CryptokiNotInitialized     => True,
      Interfac.CryptokiAlreadyInitialized => True);

   ------------------------------------------------------------------
   -- Local Subprograms
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- ConvertRetValToText
   --
   -- Description:
   --    Produces a String representing the error code
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   function ConvertRetValToText
     (RetVal : Interfac.ReturnValueT;
      Op     : CommonTypes.StringF1L1000)
     return AuditTypes.DescriptionT
   is
      Result    : AuditTypes.DescriptionT := AuditTypes.NoDescription;
      TheString : constant String :=
        "Crypto Library Error in "& Op& " : "
        & Interfac.ReturnValueT_Image (RetVal);

   begin
      if TheString'Length <= AuditTypes.DescriptionT'Last then
         Result (1 .. TheString'Length) := TheString;
      else
         Result := TheString (1 .. AuditTypes.DescriptionT'Last);
      end if;

      return Result;
   end ConvertRetValToText;

   ------------------------------------------------------------------
   -- Digest
   --
   -- Description:
   --    Attempts to digest the raw cerificate data
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Digest (Mechanism   : in     CryptoTypes.AlgorithmT;
                     RawCertData : in     CertTypes.RawDataT;
                     TheDigest   :    out Interfac.DigestT;
                     Success     :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Interfac.Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Interfac.Store,
                                               Mechanism,
                                               RawCertData),
                      (Success,
                       TheDigest)          => (Interfac.Store,
                                               Mechanism,
                                               RawCertData))
   is
      RetValIni : Interfac.ReturnValueT;
      -- Initialize the update and final returns to Ok, so a
      -- system fault isn't raised if an update is not executed.
      RetValUpd,
      RetValFin : Interfac.ReturnValueT := Interfac.Ok;

      LoopMax : Positive;
      BytesLeft : Positive;

      Block : Interfac.HundredByteArrayT;
      Size : CommonTypes.Unsigned32T := 100;


      ------------------------------------------------------------------
      -- GetBlock
      --
      -- Description:
      --    Produces the required data block from the raw certificate
      --
      -- Implementation Notes:
      --    None.
      --
      ------------------------------------------------------------------
      function GetBlock
        (Data      : CertTypes.RawCertificateT;
         BlockNo   : Positive;
         BlockSize : CommonTypes.Unsigned32T)
        return Interfac.HundredByteArrayT
        with Pre => BlockNo in 1 .. 41
                      and then BlockSize in 1 .. 100
                      and then Positive (BlockSize) + (BlockNo - 1) * 100
                        <= CertTypes.RawCertificateI'Last
      is
         Result : Interfac.HundredByteArrayT :=
           Interfac.HundredByteArrayT'(others => ' ');
      begin
         for J in CertTypes.RawCertificateI range 1 .. 100 loop
            pragma Loop_Invariant
              (BlockNo in 1 .. 41
               and BlockSize in 1 .. 100
               and CommonTypes.Unsigned32T (J) <= BlockSize);

            Result (J) := Data (J + (BlockNo - 1) * 100);

            exit when CommonTypes.Unsigned32T (J) = BlockSize;
         end loop;

         return Result;
      end GetBlock;

   begin
      TheDigest := Interfac.NullDigest;

      Interfac.DigestInit
        (Mechanism   => Mechanism,
         ReturnValue => RetValIni);

      -- is Mechanism is dom Digest?   ??? comment is not proper english

      if RetValIni = Interfac.Ok then
         -- If so perform digest...
         LoopMax := ((RawCertData.DataLength - 1) / 100) + 1;
         BytesLeft := RawCertData.DataLength;

         for J in 1 .. LoopMax loop
            pragma Loop_Invariant
              (LoopMax = ((RawCertData.DataLength - 1) / 100) + 1
               and LoopMax = LoopMax'Loop_Entry
               and J in 1 .. LoopMax
               and BytesLeft = (RawCertData.DataLength) - (J - 1) * 100
               and Size in 1 .. 100
               and RetValIni = Interfac.Ok
               and RetValFin = Interfac.Ok);

            if BytesLeft < 100 then
               Size := CommonTypes.Unsigned32T (BytesLeft);
            end if;

            Block := GetBlock
              (Data      => RawCertData.RawData,
               BlockNo   => J,
               BlockSize => Size);

            Interfac.DigestUpdate
              (DataBlock   => Block,
               ByteCount   => Size,
               ReturnValue => RetValUpd);

            exit when RetValUpd /= Interfac.Ok or J = LoopMax;

            BytesLeft := BytesLeft - 100;
         end loop;

         -- If everything OK, then get the calculated digest
         if RetValUpd = Interfac.Ok then
            Interfac.DigestFinal
              (Digest       => TheDigest,
               ReturnValue  => RetValFin);
         end if;
      end if;

      Success := RetValIni = Interfac.Ok and
                 RetValUpd = Interfac.Ok and
                 RetValFin = Interfac.Ok;

      if IsSystem (RetValIni) then
         AuditLog.AddElementToLog
           (ElementID    => AuditTypes.SystemFault,
            Severity     => AuditTypes.Warning,
            User         => AuditTypes.NoUser,
            Description  => ConvertRetValToText(RetValIni, "DigestInit"));
      end if;

      if IsSystem (RetValUpd) then
         AuditLog.AddElementToLog
           (ElementID    => AuditTypes.SystemFault,
            Severity     => AuditTypes.Warning,
            User         => AuditTypes.NoUser,
            Description  => ConvertRetValToText(RetValUpd, "DigestUpdate"));
      end if;

      if IsSystem (RetValFin) then
         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.SystemFault,
            Severity    => AuditTypes.Warning,
            User        => AuditTypes.NoUser,
            Description => ConvertRetValToText(RetValFin, "DigestFinal"));
      end if;
   end Digest;

   ------------------------------------------------------------------
   -- DoFind
   --
   -- Description:
   --    Calls the Crypto Find operations in order, and attempts to find
   --    HandleCount handles.Returns these in a HandleArray and a
   --    count of the actual number found.
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure DoFind
     (Template    : in     Interfac.KeyTemplateT;
      HandleCount : in out CommonTypes.Unsigned32T;
      Handles     :    out Interfac.HandleArrayT)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Interfac.Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State) => (AuditLog.FileState,
                                           AuditLog.State,
                                           Clock.Now,
                                           ConfigData.State,
                                           HandleCount,
                                           Interfac.Store,
                                           Template),
                      (HandleCount,
                       Handles)     => (HandleCount,
                                        Interfac.Store,
                                        Template))
   is
      RetValIni : Interfac.ReturnValueT;
      -- Initialize the find and final returns to Ok, so a
      -- system fault isn't raised if a FindObjects is not executed.
      RetValDo,
      RetValFin : Interfac.ReturnValueT := Interfac.Ok;
   begin
      Handles := Interfac.HandleArrayT'(others => NullKey);
      Interfac.FindObjectsInit(Template    => Template,
                               ReturnValue => RetValIni);

      if RetValIni = Interfac.Ok then
         Interfac.FindObjects(HandleCount   => HandleCount,
                              ObjectHandles => Handles,
                              ReturnValue   => RetValDo);

         if RetValIni = Interfac.Ok then
            Interfac.FindObjectsFinal(ReturnValue => RetValFin);
         end if;
      end if;

      if IsSystem (RetValIni) then
         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.SystemFault,
            Severity    => AuditTypes.Warning,
            User        => AuditTypes.NoUser,
            Description => ConvertRetValToText (RetValIni, "FindObjectsInit "));
      end if;

      if IsSystem (RetValDo) then
         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.SystemFault,
            Severity    => AuditTypes.Warning,
            User        => AuditTypes.NoUser,
            Description => ConvertRetValToText(RetValDo, "FindObjects "));
      end if;

      if IsSystem (RetValFin) then
         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.SystemFault,
            Severity    => AuditTypes.Warning,
            User        => AuditTypes.NoUser,
            Description => ConvertRetValToText(RetValFin, "FindObjectsFinal "));
      end if;
   end DoFind;

   ------------------------------------------------------------------
   -- KeyMatchingIssuer
   --
   -- Description:
   --    Searches for a public key belonging to the issuer in the
   --    crypto library.
   --    IssuerKey is set to null if a key wasn't found.
   --
   -- Implementation Notes:
   --    If more than one found, a system fault is raised, but the
   --    first handle is returned, and the TIS is allowed to continue.
   --
   ------------------------------------------------------------------
   procedure KeyMatchingIssuer (Issuer    : in     CryptoTypes.IssuerT;
                                IssuerKey :    out CommonTypes.Unsigned32T)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Interfac.Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Interfac.Store,
                                               Issuer),
                      IssuerKey            => (Interfac.Store,
                                               Issuer))
   is
      IssuerTemplate : Interfac.KeyTemplateT;
      Handles : Interfac.HandleArrayT;

      -- Only expect to find one public key belonging to the issuer
      ExpectedCount : constant CommonTypes.Unsigned32T := 1;
      ActualCount   : CommonTypes.Unsigned32T := ExpectedCount;

   begin
      -- Create a crypto template, with only the Owner attr defined.
      IssuerTemplate := Interfac.KeyTemplateT'(
                           AttrMask  => Interfac.OwnerMask or
                                        Interfac.IsPublicMask,
                           Owner     => Issuer,
                           KeyID     => 0,
                           KeyLength => 0,
                           IsPublic  => True);

      DoFind(Template    => IssuerTemplate,
             HandleCount => ActualCount,
             Handles     => Handles);

      if ActualCount > ExpectedCount then

         -- More than one key matched.
         AuditLog.AddElementToLog(
                ElementID   => AuditTypes.SystemFault,
                Severity    => AuditTypes.Warning,
                User        => AuditTypes.NoUser,
                Description => "Crypto Library Error : Library holds "&
                               "more than one public key for an Issuer."
                );
      end if;

      -- If a key wasn't found, the crypto library sets this to the NullKey
      -- value.
      IssuerKey := Handles(1);

   end KeyMatchingIssuer;

   ------------------------------------------------------------------
   -- PrivateKey
   --
   -- Description:
   --    Searches for a private key in the crypto library.
   --    PrivateKeyHandle is set to null if a key wasn't found.
   --
   -- Implementation Notes:
   --    If more than one found, a system fault is raised, but the
   --    first handle is returned, and the TIS is allowed to continue.
   --
   ------------------------------------------------------------------
   procedure PrivateKey (PrivateKeyHandle :    out CommonTypes.Unsigned32T)
     with Global  => (Input  => (Clock.Now,
                                  ConfigData.State,
                                  Interfac.Store),
                       In_Out => (AuditLog.FileState,
                                  AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Interfac.Store),
                      PrivateKeyHandle     => Interfac.Store)
   is
      PrivateTemplate : Interfac.KeyTemplateT;
      Handles : Interfac.HandleArrayT;

      -- Only expect to find one public key belonging to the issuer
      ExpectedCount : constant CommonTypes.Unsigned32T := 1;
      ActualCount   : CommonTypes.Unsigned32T := ExpectedCount;

   begin
      -- Create a crypto template, with only the IsPublic attr defined.
      PrivateTemplate := Interfac.KeyTemplateT'(
                            AttrMask  => Interfac.IsPublicMask,
                            Owner     => CryptoTypes.NullIssuer,
                            KeyID     => 0,
                            KeyLength => 0,
                            IsPublic  => False);

      DoFind(Template    => PrivateTemplate,
             HandleCount => ActualCount,
             Handles     => Handles);

      if ActualCount > ExpectedCount then

         -- More than one key matched.
         AuditLog.AddElementToLog(
                ElementID   => AuditTypes.SystemFault,
                Severity    => AuditTypes.Warning,
                User        => AuditTypes.NoUser,
                Description => "Crypto Library Error : Library holds "&
                               "more than one private key for this TIS."
                );
      end if;

      PrivateKeyHandle := Handles(1);

   end PrivateKey;

   ------------------------------------------------------------------
   -- Exported Subprograms
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Init
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Interfac.Store),
                              Output => ThisTISInfo,
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.Store),
                              ThisTISInfo          => Interfac.Store)
   is
      RetVal : Interfac.ReturnValueT;
      ThePrivateKeyH : CommonTypes.Unsigned32T;

      ThePrivateKey : Interfac.KeyTemplateT :=
                         Interfac.KeyTemplateT'(
                            AttrMask  => Interfac.OwnerMask,
                            Owner     => CryptoTypes.NullIssuer,
                            KeyID     => 0,
                            KeyLength => 0,
                            IsPublic  => False);
   begin
      Interfac.Initialize(ReturnValue => RetVal);
      if IsSystem(RetVal) then

         AuditLog.AddElementToLog(
                ElementID   => AuditTypes.SystemFault,
                Severity    => AuditTypes.Warning,
                User        => AuditTypes.NoUser,
                Description => ConvertRetValToText(RetVal, "Initialize")
                );
      end if;

      PrivateKey(PrivateKeyHandle => ThePrivateKeyH);

      ThisTISInfo.IsPresent := (ThePrivateKeyH /= NullKey);

      if ThisTISInfo.IsPresent then
         Interfac.GetAttributeValue(KeyHandle   => ThePrivateKeyH,
                                    Template    => ThePrivateKey,
                                    ReturnValue => RetVal);

         if RetVal = Interfac.Ok then
            ThisTISInfo.Owner := ThePrivateKey.Owner;
         else
            ThisTISInfo.Owner := CryptoTypes.NullIssuer;
         end if;
      else
         ThisTISInfo.Owner := CryptoTypes.NullIssuer;
      end if;
   end Init;

   ------------------------------------------------------------------
   -- KeyMatchingIssuerPresent
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure KeyMatchingIssuerPresent(Issuer    : in     CryptoTypes.IssuerT;
                                      IsPresent :    out Boolean)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Interfac.Store),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.Store,
                                                       Issuer),
                              IsPresent            => (Interfac.Store,
                                                       Issuer))
   is
      TheIssuerKey : CommonTypes.Unsigned32T;
   begin

      KeyMatchingIssuer(Issuer    => Issuer,
                        IssuerKey => TheIssuerKey);
      IsPresent := (TheIssuerKey /= NullKey);

   end KeyMatchingIssuerPresent;

   ------------------------------------------------------------------
   -- IsVerifiedBy
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure IsVerifiedBy (Mechanism   : in     CryptoTypes.AlgorithmT;
                           RawCertData : in     CertTypes.RawDataT;
                           Signature   : in     CertTypes.SignatureT;
                           TheIssuer   : in     CryptoTypes.IssuerT;
                           Verified    :    out Boolean)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Interfac.Store),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.Store,
                                                       Mechanism,
                                                       RawCertData,
                                                       Signature,
                                                       TheIssuer),
                              Verified             => (Interfac.Store,
                                                       Mechanism,
                                                       RawCertData,
                                                       Signature,
                                                       TheIssuer))
   is
      TheDigest    : Interfac.DigestT;
      Digested     : Boolean;
      TheIssuerKey : CommonTypes.Unsigned32T;
      RetVal       : Interfac.ReturnValueT;
   begin
      Digest(Mechanism   => Mechanism,
             RawCertData => RawCertData,
             TheDigest   => TheDigest,
             Success     => Digested);

      if Digested then
         KeyMatchingIssuer(Issuer    => TheIssuer,
                           IssuerKey => TheIssuerKey);

         Interfac.Verify(Mechanism    => Mechanism,
                       KeyHandle    => TheIssuerKey,
                       Digest       => TheDigest,
                       Signature    => Signature,
                       ReturnValue  => RetVal);

         Verified := (RetVal = Interfac.Ok);

         if IsSystem(RetVal) then
            AuditLog.AddElementToLog(
                   ElementID    => AuditTypes.SystemFault,
                   Severity     => AuditTypes.Warning,
                   User         => AuditTypes.NoUser,
                   Description  => ConvertRetValToText(RetVal, "Verify")
                   );
         end if;

      else
         -- Digest has failed -
         -- the Digest subprogram adds an entry to the audit log if
         -- there is a system fault
         Verified := False;
      end if;

   end IsVerifiedBy;

   ------------------------------------------------------------------
   -- Sign
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Sign (RawCertData : in     CertTypes.RawDataT;
                   Signature   :    out CertTypes.SignatureT;
                   Signed      :    out Boolean)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Interfac.Store),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.Store,
                                                       RawCertData),
                              (Signature,
                               Signed)             => (Interfac.Store,
                                                       RawCertData))
   is
      -- This TIS always uses RSA with SHA-1
      Mechanism : constant CryptoTypes.AlgorithmT := CryptoTypes.SHA1_RSA;
      ThePrivateKeyH : CommonTypes.Unsigned32T;
      TheDigest : Interfac.DigestT;

      Digested  : Boolean;
      RetVal    : Interfac.ReturnValueT;
   begin
      Digest(Mechanism   => Mechanism,
             RawCertData => RawCertData,
             TheDigest   => TheDigest,
             Success     => Digested);

      if Digested then
         PrivateKey(PrivateKeyHandle => ThePrivateKeyH);

#if SECURITY_DEMO
         --  information leak: display the value of the private key
         declare
            Unused : Boolean;
         begin
            DisplayAPI.SetBottomText
              (BottomText => "Private key " &
                 CommonTypes.Unsigned32T_Image (ThePrivateKeyH),
               Written    => Unused);
         end;
#end if;

         Interfac.Sign(Mechanism   => Mechanism,
                       KeyHandle   => ThePrivateKeyH,
                       Digest      => TheDigest,
                       Signature   => Signature,
                       ReturnValue => RetVal
                      );
         Signed := (Retval = Interfac.Ok);

         if IsSystem(RetVal) then
            AuditLog.AddElementToLog(
                   ElementID   => AuditTypes.SystemFault,
                   Severity    => AuditTypes.Warning,
                   User        => AuditTypes.NoUser,
                   Description => ConvertRetValToText(RetVal, "Sign")
                   );
         end if;

      else
         -- Digest has failed -
         -- the Digest subprogram adds an entry to the audit log if
         -- there is a system fault
         Signed := False;
         Signature :=
           CertTypes.SignatureT'
             (SigData   => CertTypes.SigDataT'(others => ' '),
              SigLength => 1);
      end if;

   end Sign;

   ------------------------------------------------------------------
   -- AddKey
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure AddKey (TheOwner : in     CryptoTypes.IssuerT;
                     TheKey   : in     CryptoTypes.KeyPartT;
                     IsPublic : in     Boolean;
                     Added    :    out Boolean)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         Interfac.Store,
                                         ThisTISInfo)),
          Refined_Depends => ((Added,
                               Interfac.Store)     => (Interfac.Store,
                                                       IsPublic,
                                                       TheKey,
                                                       TheOwner),
                              (AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.Store,
                                                       IsPublic,
                                                       TheKey,
                                                       TheOwner),
                              ThisTISInfo          =>+ (Interfac.Store,
                                                        IsPublic,
                                                        TheKey,
                                                        TheOwner))
   is
      TheKeyTemplate : Interfac.KeyTemplateT;
      RetVal         : Interfac.ReturnValueT;
   begin
      -- Create a crypto template.
      TheKeyTemplate :=
        Interfac.KeyTemplateT'(AttrMask  => Interfac.FullKeyMask,
                               Owner     => TheOwner,
                               KeyID     =>
                                 CommonTypes.Unsigned32T(TheKey.KeyID),
                               KeyLength =>
                                 CommonTypes.Unsigned32T(TheKey.KeyLength),
                               IsPublic  => IsPublic);

      Interfac.CreateObject(Template     => TheKeyTemplate,
                             ReturnValue => RetVal);

      Added := (RetVal = Interfac.Ok);

      if Added and not IsPublic then

         -- Have just added the TIS private key
         -- store this TIS' info.
         ThisTISInfo := OptionalPrivateKeyT'(
                            IsPresent => True,
                            Owner     => TheOwner);
      end if;

      if IsSystem(RetVal) then
         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => ConvertRetValToText(RetVal, "AddKey")
                );
      end if;
   end AddKey;

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
     with Refined_Global  => (Output => ThisTISInfo,
                              In_Out => Interfac.Store),
          Refined_Depends => (Interfac.Store =>+ null,
                              ThisTISInfo    => null)
   is
   begin
      Interfac.Delete;

      ThisTISInfo := OptionalPrivateKeyT'
        (IsPresent => False,
         Owner     => CryptoTypes.NullIssuer);
   end Delete;

end KeyStore;
