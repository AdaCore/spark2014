------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
--
-- Modifications to proof annotations by Phil Thornley, April 2009
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
     BasicTypes,
     CryptoTypes,
     KeyStore.Interface;

use type BasicTypes.Unsigned32T;
use type CryptoTypes.IssuerT;
use type KeyStore.Interface.ReturnValueT;
use type KeyStore.Interface.MaskT;

package body KeyStore
--# Own Store is KeyStore.Interface.Store &
--#     State is ThisTISInfo;
is

   ----------------------------------------------------------------
   -- Types
   ----------------------------------------------------------------
   type OptionalPrivateKeyT is record
      IsPresent : Boolean;
      Owner     : CryptoTypes.IssuerT;
   end record;

   type IsSystemT is array (Interface.ReturnValueT) of Boolean;

   ----------------------------------------------------------------
   -- State
   ----------------------------------------------------------------

   ThisTISInfo : OptionalPrivateKeyT;


   -- Key handles are unsigned 32 bit words, with zero being a null
   -- key handle.
   NullKey : constant BasicTypes.Unsigned32T := 0;

   -- Crypto errors can be groupes as a System Error, or a User Error.
   IsSystem : constant IsSystemT := IsSystemT'(
                 Interface.Ok                         => False,
                 Interface.HostMemory                 => True,
                 Interface.GeneralError               => True,
                 Interface.FunctionFailed             => True,
                 Interface.ArgumentsBad               => False,
                 Interface.AttributeReadOnly          => False,
                 Interface.AttributeTypeInvalid       => False,
                 Interface.AttributeValueInvalid      => False,
                 Interface.DataInvalid                => False,
                 Interface.DataLenRange               => False,
                 Interface.DeviceError                => True,
                 Interface.DeviceMemory               => True,
                 Interface.FunctionCanceled           => True,
                 Interface.KeyHandleInvalid           => False,
                 Interface.KeySizeRange               => False,
                 Interface.KeyTypeInconsistent        => False,
                 Interface.KeyFunctionNotPermitted    => False,
                 Interface.MechanismInvalid           => False,
                 Interface.MechanismParamInvalid      => False,
                 Interface.ObjectHandleInvalid        => False,
                 Interface.OperationActive            => True,
                 Interface.OperationNotInitialized    => True,
                 Interface.SignatureInvalid           => False,
                 Interface.SignatureLenRange          => False,
                 Interface.TemplateIncomplete         => False,
                 Interface.TemplateInconsistent       => False,
                 Interface.BufferTooSmall             => True,
                 Interface.CryptokiNotInitialized     => True,
                 Interface.CryptokiAlreadyInitialized => True
                 );


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
   function ConvertRetValToText(RetVal : Interface.ReturnValueT;
                                Op     : String) return AuditTypes.DescriptionT
   is
   --# hide ConvertRetValToText;
      Result : AuditTypes.DescriptionT := AuditTypes.NoDescription;
      TheString : String := "Crypto Library Error in " & Op & " : " &
                               Interface.ReturnValueT'Image(RetVal);
   begin
      if TheString'Length <= AuditTypes.DescriptionT'Last then
         Result(1..TheString'Length) := TheString;
      else
         Result := TheString(1..AuditTypes.DescriptionT'Last);
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
   procedure Digest(Mechanism   : in     CryptoTypes.AlgorithmT;
                    RawCertData : in     CertTypes.RawDataT;
                    TheDigest   :    out Interface.DigestT;
                    Success     :    out Boolean)
   --# global in     Interface.Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives TheDigest,
   --#         Success            from Mechanism,
   --#                                 RawCertData,
   --#                                 Interface.Store &
   --#         AuditLog.State,
   --#         AuditLog.FileState from Mechanism,
   --#                                 RawCertData,
   --#                                 Interface.Store,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State;
   is
      RetValIni : Interface.ReturnValueT;
      -- Initialize the update and final returns to Ok, so a
      -- system fault isn't raised if an update is not executed.
      RetValUpd,
      RetValFin : Interface.ReturnValueT := Interface.Ok;

      LoopMax : Positive;
      BytesLeft : Positive;

      Block : Interface.HundredByteArrayT;
      Size : BasicTypes.Unsigned32T := 100;


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
      function GetBlock(Data      : CertTypes.RawCertificateT;
                        BlockNo   : Positive;
                        BlockSize : BasicTypes.Unsigned32T)
                  return Interface.HundredByteArrayT
      --# pre 1 <= BlockNo and
      --#     BlockNo <= 41 and
      --#     1 <= BlockSize and
      --#     BlockSize <= 100 and
      --#     Positive(BlockSize) + (BlockNo - 1) * 100 <= CertTypes.RawCertificateI'Last;
      is
         Result : Interface.HundredByteArrayT :=
                     Interface.HundredByteArrayT'(others => ' ');
      begin
         for i in CertTypes.RawCertificateI range 1 .. 100 loop
            --# assert 1 <= BlockNo and
            --#        BlockNo <= 41 and
            --#        1 <= BlockSize and
            --#        BlockSize <= 100 and
            --#        1 <= i and i <= 100 and
            --#        BasicTypes.Unsigned32T(i) <= BlockSize;

            --# check i + (BlockNo - 1) * 100 in 1 .. 4096;
            Result(i) := Data(i + (BlockNo - 1) * 100);
            exit when BasicTypes.Unsigned32T(i) = BlockSize;
         end loop;

         return Result;
      end GetBlock;


   begin
      TheDigest := Interface.NullDigest;

      Interface.DigestInit(Mechanism   => Mechanism,
                           ReturnValue => RetValIni);
      -- is Mechanism is dom Digest?
      if RetValIni = Interface.Ok then

         -- If so perform digest...
         LoopMax := ( (RawCertData.DataLength - 1) / 100 ) + 1;
         BytesLeft := RawCertData.DataLength;

         --# check LoopMax <= 41;

         for i in Positive range 1..LoopMax loop

            --# assert LoopMax = ((RawCertData.DataLength - 1) / 100) + 1 and
            --#        LoopMax = LoopMax% and
            --#        LoopMax% <= 41 and
            --#        1 <= i and i <= LoopMax and
            --#        BytesLeft = (RawCertData.DataLength) - (i - 1) * 100 and
            --#        (BytesLeft <= 100 -> i = LoopMax%) and
            --#        (i = 41 -> BytesLeft <= 96) and
            --#        1 <= RawCertData.DataLength and
            --#        RawCertData.DataLength <= 4096 and
            --#        1 <= Size and Size <= 100 and
            --#        RetValIni = Interface.Ok and
            --#        RetValFin = Interface.Ok;

            if BytesLeft < 100 then
               Size := BasicTypes.Unsigned32T(BytesLeft);
            end if;

            Block := GetBlock(Data      => RawCertData.RawData,
                              BlockNo   => i,
                              BlockSize => Size);

            Interface.DigestUpdate(DataBlock   => Block,
                                   ByteCount   => Size,
                                   ReturnValue => RetValUpd);

            exit when RetValUpd /= Interface.Ok or
                   i = LoopMax;

            --# check BytesLeft /= 100;

            BytesLeft := BytesLeft - 100;

         end loop;

         -- If everything OK, then get the calculated digest
         if RetValUpd = Interface.Ok then

            Interface.DigestFinal(Digest       => TheDigest,
                                  ReturnValue  => RetValFin);
         end if;
      end if;
      --# assert True;

      Success := RetValIni = Interface.Ok and
                 RetValUpd = Interface.Ok and
                 RetValFin = Interface.Ok;

      if IsSystem(RetValIni) then
         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => ConvertRetValToText(RetValIni, "DigestInit")
                );
      end if;

      if IsSystem(RetValUpd) then
         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => ConvertRetValToText(RetValUpd, "DigestUpdate")
                );
      end if;

      if IsSystem(RetValFin) then
         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => ConvertRetValToText(RetValFin, "DigestFinal")
                );
      end if;
   end Digest;


   ------------------------------------------------------------------
   -- DoFind
   --
   -- Description:
   --    Calls the Crypto Find operations in order, and attempts to find
   --    HandleCount handles. Returns these in a HandleArray and a
   --    count of the actual number found.
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure DoFind(Template    : in     Interface.KeyTemplateT;
                    HandleCount : in out BasicTypes.Unsigned32T;
                    Handles     :    out Interface.HandleArrayT)
   --# global in     Interface.Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from Interface.Store,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 HandleCount,
   --#                                 Template &
   --#         HandleCount,
   --#         Handles            from Interface.Store,
   --#                                 HandleCount,
   --#                                 Template;
   is
      RetValIni : Interface.ReturnValueT;
      -- Initialize the find and final returns to Ok, so a
      -- system fault isn't raised if a FindObjects is not executed.
      RetValDo,
      RetValFin : Interface.ReturnValueT := Interface.Ok;
   begin
      Handles := Interface.HandleArrayT'(others => NullKey);
      Interface.FindObjectsInit(Template    => Template,
                             ReturnValue => RetValIni);

      if RetValIni = Interface.Ok then
         Interface.FindObjects(HandleCount   => HandleCount,
                               ObjectHandles => Handles,
                               ReturnValue   => RetValDo);

         if RetValIni = Interface.Ok then
            Interface.FindObjectsFinal(ReturnValue => RetValFin);
         end if;
      end if;

      if IsSystem(RetValIni) then

         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => ConvertRetValToText(RetValIni, "FindObjectsInit ")
                );
      end if;

      if IsSystem(RetValDo) then

         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => ConvertRetValToText(RetValDo, "FindObjects ")
                );
      end if;

      if IsSystem(RetValFin) then

         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => ConvertRetValToText(RetValFin, "FindObjectsFinal ")
                );
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
   procedure KeyMatchingIssuer(Issuer    : in     CryptoTypes.IssuerT;
                               IssuerKey :    out BasicTypes.Unsigned32T)
   --# global in     Interface.Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from Interface.Store,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Issuer &
   --#         IssuerKey          from Interface.Store,
   --#                                 Issuer;
   is
      IssuerTemplate : Interface.KeyTemplateT;
      Handles : Interface.HandleArrayT;

      -- Only expect to find one public key belonging to the issuer
      ExpectedCount : constant BasicTypes.Unsigned32T := 1;
      ActualCount   : BasicTypes.Unsigned32T := ExpectedCount;

   begin
      -- Create a crypto template, with only the Owner attr defined.
      IssuerTemplate := Interface.KeyTemplateT'(
                           AttrMask  => Interface.OwnerMask or
                                        Interface.IsPublicMask,
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
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => "Crypto Library Error : Library holds " &
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
   procedure PrivateKey(PrivateKeyHandle :    out BasicTypes.Unsigned32T)
   --# global in     Interface.Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from Interface.Store,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         PrivateKeyHandle   from Interface.Store;
   is
      PrivateTemplate : Interface.KeyTemplateT;
      Handles : Interface.HandleArrayT;

      -- Only expect to find one public key belonging to the issuer
      ExpectedCount : constant BasicTypes.Unsigned32T := 1;
      ActualCount   : BasicTypes.Unsigned32T := ExpectedCount;

   begin
      -- Create a crypto template, with only the IsPublic attr defined.
      PrivateTemplate := Interface.KeyTemplateT'(
                            AttrMask  => Interface.IsPublicMask,
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
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => "Crypto Library Error : Library holds " &
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
   --# global in     Interface.Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out ThisTISInfo;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from Interface.Store,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         ThisTISInfo        from Interface.Store;
   is
      RetVal : Interface.ReturnValueT;
      ThePrivateKeyH : BasicTypes.Unsigned32T;

      ThePrivateKey : Interface.KeyTemplateT :=
                         Interface.KeyTemplateT'(
                            AttrMask  => Interface.OwnerMask,
                            Owner     => CryptoTypes.NullIssuer,
                            KeyID     => 0,
                            KeyLength => 0,
                            IsPublic  => False);
   begin
      Interface.Initialize(ReturnValue => RetVal);
      if IsSystem(RetVal) then

         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Warning,
                User         => AuditTypes.NoUser,
                Description  => ConvertRetValToText(RetVal, "Initialize")
                );
      end if;

      PrivateKey(PrivateKeyHandle => ThePrivateKeyH);

      ThisTISInfo.IsPresent := (ThePrivateKeyH /= NullKey);

      if ThisTISInfo.IsPresent then
         Interface.GetAttributeValue(KeyHandle   => ThePrivateKeyH,
                                     Template    => ThePrivateKey,
                                     ReturnValue => RetVal);

         if RetVal = Interface.Ok then
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
   --# global in     Interface.Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from Interface.Store,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Issuer &
   --#         IsPresent          from Interface.Store,
   --#                                 Issuer;
   is
      TheIssuerKey : BasicTypes.Unsigned32T;
   begin

      KeyMatchingIssuer(Issuer    => Issuer,
                        IssuerKey => TheIssuerKey);
      IsPresent := (TheIssuerKey /= NullKey);

   end KeyMatchingIssuerPresent;


   ------------------------------------------------------------------
   -- PrivateKeyPresent
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function PrivateKeyPresent return Boolean
   --# global ThisTISInfo;
   is
   begin
      return ThisTISInfo.IsPresent;
   end PrivateKeyPresent;


   ------------------------------------------------------------------
   -- IssuerIsThisTIS
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function IssuerIsThisTIS(Issuer : in     CryptoTypes.IssuerT)
     return  Boolean
   --# global ThisTISInfo;
   is
      IsTIS : Boolean;
   begin
      if PrivateKeyPresent then
         IsTIS := (Issuer = ThisTISInfo.Owner);
      else
         IsTIS := False;
      end if;
      return IsTIS;
   end IssuerIsThisTIS;


   ------------------------------------------------------------------
   -- ThisTIS
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function ThisTIS return CryptoTypes.IssuerT
   --# global ThisTISInfo;
   is
   begin
      return ThisTISInfo.Owner;
   end ThisTIS;


   ------------------------------------------------------------------
   -- IsVerifiedBy
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure  IsVerifiedBy(Mechanism   : in     CryptoTypes.AlgorithmT;
                           RawCertData : in     CertTypes.RawDataT;
                           Signature   : in     CertTypes.SignatureT;
                           TheIssuer   : in     CryptoTypes.IssuerT;
                           Verified    :    out Boolean)
   --# global in     Interface.Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from Mechanism,
   --#                                 RawCertData,
   --#                                 Interface.Store,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 TheIssuer,
   --#                                 Signature &
   --#         Verified           from Mechanism,
   --#                                 RawCertData,
   --#                                 Interface.Store,
   --#                                 TheIssuer,
   --#                                 Signature;
   is
      TheDigest    : Interface.DigestT;
      Digested     : Boolean;
      TheIssuerKey : BasicTypes.Unsigned32T;
      RetVal       : Interface.ReturnValueT;
   begin
      Digest(Mechanism   => Mechanism,
             RawCertData => RawCertData,
             TheDigest   => TheDigest,
             Success     => Digested);

      if Digested then
         KeyMatchingIssuer(Issuer    => TheIssuer,
                           IssuerKey => TheIssuerKey);

         Interface.Verify(Mechanism    => Mechanism,
                       KeyHandle    => TheIssuerKey,
                       Digest       => TheDigest,
                       Signature    => Signature,
                       ReturnValue  => RetVal);

         Verified := (RetVal = Interface.Ok);

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
   procedure  Sign(RawCertData : in     CertTypes.RawDataT;
                   Signature   :    out CertTypes.SignatureT;
                   Signed      :    out Boolean)
   --# global in     Interface.Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from RawCertData,
   --#                                 Interface.Store,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         Signature,
   --#         Signed             from RawCertData,
   --#                                 Interface.Store;
   is
      -- This TIS always uses RSA with SHA-1
      Mechanism : constant CryptoTypes.AlgorithmT := CryptoTypes.SHA1_RSA;
      ThePrivateKeyH : BasicTypes.Unsigned32T;
      TheDigest : Interface.DigestT;

      Digested  : Boolean;
      RetVal    : Interface.ReturnValueT;
   begin
      Digest(Mechanism   => Mechanism,
             RawCertData => RawCertData,
             TheDigest   => TheDigest,
             Success     => Digested);

      if Digested then
         PrivateKey(PrivateKeyHandle => ThePrivateKeyH);

         Interface.Sign(Mechanism    => Mechanism,
                     KeyHandle    => ThePrivateKeyH,
                     Digest       => TheDigest,
                     Signature    => Signature,
                     ReturnValue  => RetVal
                     );
         Signed := (Retval = Interface.Ok);

         if IsSystem(RetVal) then
            AuditLog.AddElementToLog(
                   ElementID    => AuditTypes.SystemFault,
                   Severity     => AuditTypes.Warning,
                   User         => AuditTypes.NoUser,
                   Description  => ConvertRetValToText(RetVal, "Sign")
                   );
         end if;

      else
         -- Digest has failed -
         -- the Digest subprogram adds an entry to the audit log if
         -- there is a system fault
         Signed := False;
         Signature := CertTypes.SignatureT'(SigData   => CertTypes.SigDataT'(others => ' '),
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
   procedure AddKey(TheOwner : in     CryptoTypes.IssuerT;
                    TheKey   : in     CryptoTypes.KeyPartT;
                    IsPublic : in     Boolean;
                    Added    :    out Boolean)
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out Interface.Store;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out ThisTISInfo;
   --# derives Interface.Store,
   --#         ThisTISInfo        from *,
   --#                                 Interface.Store,
   --#                                 TheOwner,
   --#                                 TheKey,
   --#                                 IsPublic &
   --#         AuditLog.State,
   --#         AuditLog.FileState from Interface.Store,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 TheOwner,
   --#                                 TheKey,
   --#                                 IsPublic &
   --#         Added              from Interface.Store,
   --#                                 TheOwner,
   --#                                 TheKey,
   --#                                 IsPublic;
   --# post ((Added and not IsPublic) -> PrivateKeyPresent(ThisTISInfo)) and
   --#      (not (Added and not IsPublic) -> PrivateKeyPresent(ThisTISInfo) =
   --#                                        PrivateKeyPresent(ThisTISInfo~));
   is
      TheKeyTemplate : Interface.KeyTemplateT;
      RetVal : Interface.ReturnValueT;
   begin
      -- Create a crypto template.
      TheKeyTemplate := Interface.KeyTemplateT'(
                           AttrMask  => Interface.FullKeyMask,
                           Owner     => TheOwner,
                           KeyID     => BasicTypes.Unsigned32T(TheKey.KeyID),
                           KeyLength => BasicTypes.Unsigned32T(TheKey.KeyLength),
                           IsPublic  => IsPublic);

      Interface.CreateObject(Template     => TheKeyTemplate,
                             ReturnValue  => RetVal);

      Added := (RetVal = Interface.Ok);

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
   --# global in out Interface.Store;
   --#           out ThisTISInfo;
   --# derives Interface.Store from * &
   --#         ThisTISInfo     from ;
   --# post not PrivateKeyPresent(ThisTISInfo);
   is
   begin

      Interface.Delete;

      ThisTISInfo := OptionalPrivateKeyT'(
                         IsPresent => False,
                         Owner     => CryptoTypes.NullIssuer);
   end Delete;

end KeyStore;
