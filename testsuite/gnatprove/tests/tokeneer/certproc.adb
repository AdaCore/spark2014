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
-- CertProc
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------

with CommonTypes;
with MsgProc;
with CryptoTypes;
with Ada.Strings.Fixed;
with Ada.Strings;

use type CommonTypes.Unsigned32T;
use type CryptoTypes.AlgorithmT;
use type CryptoTypes.IssuerT;

package body CertProc
  with SPARK_Mode => Off  --  exception handlers
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------
   CryptoControlData : CryptoControlDataT := NullCryptoControl;

   subtype RoleValues is Integer range 0..3;
   type RoleFromT is array(RoleValues) of PrivTypes.PrivilegeT;
   type RoleToT is array(PrivTypes.PrivilegeT) of RoleValues;

   subtype ClassValues is Integer range 0..5;
   type ClassFromT is array(ClassValues) of PrivTypes.ClassT;
   type ClassToT is array (PrivTypes.ClassT) of ClassValues;

   RoleFrom : constant RoleFromT := (
       0 => PrivTypes.UserOnly,
       1 => PrivTypes.Guard,
       2 => PrivTypes.SecurityOfficer,
       3 => PrivTypes.AuditManager
      );

   RoleTo : constant RoleToT := (
       PrivTypes.UserOnly        => 0,
       PrivTypes.Guard           => 1,
       PrivTypes.SecurityOfficer => 2,
       PrivTypes.AuditManager    => 3
      );

   ClassFrom : constant ClassFromT := (
       0 => PrivTypes.Unmarked,
       1 => PrivTypes.Unclassified,
       2 => PrivTypes.Restricted,
       3 => PrivTypes.Confidential,
       4 => PrivTypes.Secret,
       5 => PrivTypes.Topsecret
      );

   ClassTo : constant ClassToT := (
       PrivTypes.Unmarked => 0,
       PrivTypes.Unclassified => 1,
       PrivTypes.Restricted => 2,
       PrivTypes.Confidential => 3,
       PrivTypes.Secret => 4,
       PrivTypes.Topsecret => 5
      );

   ------------------------------------------------------------------
   -- Local Subprograms
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- Extractname
   --
   -- Description:
   --    Extracts the values from TheDict and checks the values are
   --    in type. If values are invalid, or there is a problem extracting
   --    the values, then NullIssuer is returned.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ExtractName(TheDict : in     MsgProc.DictionaryT;
                         TheName :    out CryptoTypes.IssuerT)
   is
      TheNameString : String := MsgProc.GetStringByKey(
                                     Dic => TheDict,
                                     Key => "Text");
      TheNameLength : Integer;
   begin
      TheNameLength := Integer'Value(
                          MsgProc.GetStringByKey(
                                     Dic => TheDict,
                                     Key => "TextLength"));

      if TheNameLength <= CryptoTypes.NameI'Last then

         TheName.NameLength := TheNameLength;
         TheName.Name :=
                -- Truncate the name if it is longer than the length
                -- given
                Ada.Strings.Fixed.Overwrite(
                           CryptoTypes.BlankName,
                           1,
                           Ada.Strings.Fixed.Head(TheNameString,
                                                  TheNameLength));

         TheName.ID := CryptoTypes.IssuerIDT'Value(
                          MsgProc.GetStringByKey(
                                Dic => TheDict,
                                Key => "ID"));
      else
         TheName := CryptoTypes.NullIssuer;
      end if;

   exception
      when E : others =>
         TheName := CryptoTypes.NullIssuer;
   end ExtractName;

   ------------------------------------------------------------------
   -- ExtractValidity
   --
   -- Description:
   --    Extracts the NotBefore and NotAfter dictionaries from TheDict
   --    and checks the values are in type. If values are invalid, or
   --    there is a problem extracting the values, then
   --    a default value is set, and success is set False
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ExtractValidity(TheDict     : in     MsgProc.DictionaryT;
                             TheValidity :    out ValidityT;
                             Ok          :    out Boolean)
   is
      NB : MsgProc.DictionaryT :=
              MsgProc.GetDictionaryByKey(Dic => TheDict,
                                         Key => "NotBefore");
      NA : MsgProc.DictionaryT :=
              MsgProc.GetDictionaryByKey(Dic => TheDict,
                                         Key => "NotAfter");

      ------------------------------------------------------------------
      -- DateNotInType
      --
      -- Description:
      --    Checks that the values are appropriate.
      --       Minute in 0..59
      --       Hour   in 0..23
      --       Day    in 1..31
      --       Month  in 1..12
      --       Year   in 1901..2099
      --    NB does not check that values are consistent with each other
      --    (e.g. if Month is April, does not check that Day is 1..30)
      --
      -- Implementation Notes:
      --    None.
      --
      ------------------------------------------------------------------
      function DateNotInType(TheDate : TimeT) return Boolean
      is
      begin
         return TheDate.Year < 1901 or
                TheDate.Year > 2099 or
                   TheDate.Month < 1 or
                   TheDate.Month > 12 or
                      TheDate.Day < 1 or
                      TheDate.Day > 31 or
                         TheDate.Hour > 23 or
                            TheDate.Minute > 59;
      end DateNotInType;

   begin
      TheValidity.NotBefore.Minute := CommonTypes.Unsigned32T'Value(
                                         MsgProc.GetStringByKey(
                                             Dic => NB,
                                             Key => "Minute"));
      TheValidity.NotBefore.Hour   := CommonTypes.Unsigned32T'Value(
                                         MsgProc.GetStringByKey(
                                             Dic => NB,
                                             Key => "Hour"));
      TheValidity.NotBefore.Day    := CommonTypes.Unsigned32T'Value(
                                         MsgProc.GetStringByKey(
                                             Dic => NB,
                                             Key => "Day"));
      TheValidity.NotBefore.Month  := CommonTypes.Unsigned32T'Value(
                                         MsgProc.GetStringByKey(
                                             Dic => NB,
                                             Key => "Month"));
      TheValidity.NotBefore.Year   := CommonTypes.Unsigned32T'Value(
                                         MsgProc.GetStringByKey(
                                             Dic => NB,
                                             Key => "Year"));

      TheValidity.NotAfter.Minute := CommonTypes.Unsigned32T'Value(
                                         MsgProc.GetStringByKey(
                                             Dic => NA,
                                             Key => "Minute"));
      TheValidity.NotAfter.Hour   := CommonTypes.Unsigned32T'Value(
                                         MsgProc.GetStringByKey(
                                             Dic => NA,
                                             Key => "Hour"));
      TheValidity.NotAfter.Day    := CommonTypes.Unsigned32T'Value(
                                         MsgProc.GetStringByKey(
                                             Dic => NA,
                                             Key => "Day"));
      TheValidity.NotAfter.Month  := CommonTypes.Unsigned32T'Value(
                                         MsgProc.GetStringByKey(
                                             Dic => NA,
                                             Key => "Month"));
      TheValidity.NotAfter.Year   := CommonTypes.Unsigned32T'Value(
                                         MsgProc.GetStringByKey(
                                             Dic => NA,
                                             Key => "Year"));

      if DateNotInType(TheValidity.NotAfter) or
         DateNotInType(TheValidity.NotBefore) then

         Ok := False;
         TheValidity := (NotBefore => (Minute => 0,
                                       Hour   => 0,
                                       Day    => 1,
                                       Month  => 1,
                                       Year   => 1901),
                         NotAfter  => (Minute => 0,
                                       Hour   => 0,
                                       Day    => 1,
                                       Month  => 1,
                                       Year   => 1901));
      else
         Ok := True;
      end if;
   end ExtractValidity;


   ------------------------------------------------------------------
   -- RemoveHolder
   --
   -- Description:
   --    Removes the Holder dictionary from the certificate.
   --    Required when attempting to extract the Issuer, or the
   --    SerialNumber.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure RemoveHolder(TheCert : in out CertTypes.RawCertificateT)
   is
      HolderDict : MsgProc.DictionaryT :=
                      MsgProc.GetDictionaryByKey(
                              Dic => MsgProc.DictionaryT(TheCert),
                              Key => "Holder");
      HolderStart : Natural;
   begin
      HolderStart := Ada.Strings.Fixed.Index(TheCert,
                                             String(HolderDict));
      -- leave both braces, to ensure any further searches
      -- will not be broken.
      Ada.Strings.Fixed.Delete(TheCert,
                               HolderStart,
                               HolderStart + HolderDict'Length - 1);

   exception
      when E : others =>
         TheCert := (others => ' ');
   end RemoveHolder;


   ------------------------------------------------------------------
   -- CheckCertLength
   --
   -- Description:
   --    Checks the CertLength is consistent with the length
   --    of the CertData dictionary.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure CheckCertLength (TheCert  : in     CertTypes.RawCertificateT;
                              Success  :    out Boolean)
   is
      TheCertLength : Integer;
      TheCertData : constant String :=
                       String(MsgProc.GetDictionaryByKey(
                                 MsgProc.DictionaryT(TheCert),
                                 "CertDataT"));
   begin
      -- The CertLength field includes the braces enclosing the CertData dictionary
      -- so subtract 2 from the length.
      TheCertLength  := Integer'Value(MsgProc.GetStringByKey(
                                          MsgProc.DictionaryT(TheCert),
                                          "CertLength")) - 2;
      Success := TheCertData'Length = TheCertLength;
   exception
      when E : others =>
         Success := False;
   end CheckCertLength;


   ------------------------------------------------------------------
   -- GetCertType
   --
   -- Description:
   --    Determines the Certificate Type.
   --    If Actual CertType found is not the same as the Expected
   --    CertType, Success is set to False.
   --    If the CertType is not found, Actual is set to an invalid
   --    value, and Success is set to False.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetCertType (TheCert  : in     CertTypes.RawCertificateT;
                          Expected : in     CommonTypes.Unsigned32T;
                          Actual   :    out CommonTypes.Unsigned32T;
                          Success  :    out Boolean)
   is
   begin
      Actual  := CommonTypes.Unsigned32T'Value(
                    MsgProc.GetStringByKey(
                              Dic => MsgProc.DictionaryT(TheCert),
                              Key => "CertType"));
      Success := Expected = Actual;
   exception
      when E : others =>
         Actual  := CommonTypes.Unsigned32T'Last;
         Success := False;
   end GetCertType;


   ------------------------------------------------------------------
   -- GetSerialNumber
   --
   -- Description:
   --    Attempts to extract the Certificate's Serial Number.
   --    Success is set False if it is not found, or if it is invalid.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetSerialNumber (TheCert  : in     CertTypes.RawCertificateT;
                              CertType : in     CommonTypes.Unsigned32T;
                              SerialNo :    out CommonTypes.Unsigned32T;
                              Success  :    out Boolean)
   is
      LocalCert : CertTypes.RawCertificateT := TheCert;
   begin
      if CertType /= IDCertType then
         -- Need to remove the 'Holder' dictionary from the certificate,
         -- since this also contains a 'SerialNumber'.
         RemoveHolder(LocalCert);
      end if;

      SerialNo := CommonTypes.Unsigned32T'Value(
                    MsgProc.GetStringByKey(
                              Dic => MsgProc.DictionaryT(LocalCert),
                              Key => "SerialNumber"));
      Success  := True;
   exception
      when E : others =>
         SerialNo := CommonTypes.Unsigned32T'Last;
         Success  := False;
   end GetSerialNumber;


   ------------------------------------------------------------------
   -- GetSigAlgID
   --
   -- Description:
   --    Attempts to extract the Certificate's SigAlgID field.
   --    A check is made that it is equal to the AlgorithmID held in
   --    the SignatureDate field.
   --    Success is set False if it is not found, or if it is not
   --    equal to the 'SignatureData' algorithm.
   --    If either algortihm ID is not found, ID is set to 'First, and
   --    Success to false.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetSigAlgID (TheCert  : in     CertTypes.RawCertificateT;
                          ID       :    out CryptoTypes.AlgorithmT;
                          Success  :    out Boolean)
   is
      SigDict : MsgProc.DictionaryT :=
                   MsgProc.GetDictionaryByKey(
                            Dic => MsgProc.DictionaryT(TheCert),
                            Key => "SignatureData");
      IDFromSig : CryptoTypes.AlgorithmT;
   begin
      ID       := CryptoTypes.AlgorithmT'Value(
                     MsgProc.GetStringByKey(
                               Dic => MsgProc.DictionaryT(TheCert),
                               Key => "SigAlgID"));

      IDFromSig := CryptoTypes.AlgorithmT'Value(
                      MsgProc.GetStringByKey(
                                Dic => SigDict,
                                Key => "AlgoRithmID"));

      Success := ID = IDFromSig;
   exception
      when E : others =>
         ID := CryptoTypes.AlgorithmT'First;
         Success  := False;
   end GetSigAlgID;


   ------------------------------------------------------------------
   -- GetName
   --
   -- Description:
   --    Attempts to extract the Certificate's Issuer field, or
   --    Subject field, depending on CertType and IsSubject.
   --    If values are invalid, or there is a problem extracting
   --    the values, then NullIssuer is returned, and Success is set
   --    to False.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetName (TheCert   : in     CertTypes.RawCertificateT;
                      CertType  : in     CommonTypes.Unsigned32T;
                      IsSubject : in     Boolean;
                      TheName   :    out CryptoTypes.IssuerT;
                      Success   :    out Boolean)
   is
      LocalCert : CertTypes.RawCertificateT := TheCert;
   begin
      if CertType /= IDCertType and
         not IsSubject then
         -- Need to remove the 'Holder' dictionary from the certificate,
         -- since this also contains an 'Issuer'.
         RemoveHolder(LocalCert);
      end if;

      if IsSubject then
         declare
            TheDict : MsgProc.DictionaryT :=
                         MsgProc.GetDictionaryByKey(
                                    Dic => MsgProc.DictionaryT(LocalCert),
                                    Key => "Subject");
         begin
            ExtractName(TheDict, TheName);
         end;
      else
         declare
            TheDict : MsgProc.DictionaryT :=
                         MsgProc.GetDictionaryByKey(
                                    Dic => MsgProc.DictionaryT(LocalCert),
                                    Key => "Issuer");
         begin
            ExtractName(TheDict, TheName);
         end;
      end if;
      Success := TheName /= CryptoTypes.NullIssuer;
   end GetName;


   ------------------------------------------------------------------
   -- GetHolder
   --
   -- Description:
   --    Attempts to extract the Certificate's Holder field.
   --    If values are invalid, or there is a problem extracting
   --    the values, then a Null holder is returned, and Success is set
   --    to False.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetHolder (TheCert   : in     CertTypes.RawCertificateT;
                        TheHolder :    out CertTypes.IDT;
                        Success   :    out Boolean)
   is
      HolderDict : MsgProc.DictionaryT :=
                      MsgProc.GetDictionaryByKey(
                              Dic => MsgProc.DictionaryT(TheCert),
                              Key => "Holder");
   begin
      ExtractName(HolderDict, TheHolder.Issuer);
      TheHolder.SerialNumber := CertTypes.SerialNumberT'Value(
                                   MsgProc.GetStringByKey(
                                      Dic => HolderDict,
                                      Key => "SerialNumber"));
      Success  := TheHolder.Issuer /= CryptoTypes.NullIssuer;
   exception
      when E : others =>
         TheHolder := (Issuer       => CryptoTypes.NullIssuer,
                       SerialNumber => CertTypes.SerialNumberT'Last);
         Success  := False;
   end GetHolder;


   ------------------------------------------------------------------
   -- GetValidity
   --
   -- Description:
   --    Attempts to extract the Certificate's Validity field, or
   --    AttCertValidity field, depending on CertType.
   --    If values are invalid, or there is a problem extracting
   --    the values, then each value is set to 'First, and Success is
   --    set to False.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetValidity (TheCert   : in     CertTypes.RawCertificateT;
                          CertType  : in     CommonTypes.Unsigned32T;
                          Validity  :    out ValidityT;
                          Success   :    out Boolean)
   is
   begin
      if CertType = IDCertType then
         declare
            TheDict : MsgProc.DictionaryT :=
                         MsgProc.GetDictionaryByKey(
                                    Dic => MsgProc.DictionaryT(TheCert),
                                    Key => "Validity");
         begin
            ExtractValidity(TheDict, Validity, Success);
         end;
      else
         declare
            TheDict : MsgProc.DictionaryT :=
                         MsgProc.GetDictionaryByKey(
                                    Dic => MsgProc.DictionaryT(TheCert),
                                    Key => "AttCertValidity");
         begin
            ExtractValidity(TheDict, Validity, Success);
         end;
      end if;
   exception
      when E : others =>
         Success := False;
         Validity := (NotBefore => (Minute => 0,
                                    Hour   => 0,
                                    Day    => 1,
                                    Month  => 1,
                                    Year   => 1901),
                      NotAfter  => (Minute => 0,
                                    Hour   => 0,
                                    Day    => 1,
                                    Month  => 1,
                                    Year   => 1901));
   end GetValidity;


   ------------------------------------------------------------------
   -- GetKeyInfo
   --
   -- Description:
   --    Attempts to extract the Certificate's SubjectPublicKeyInfo
   --    field.
   --    If there is a problem extracting the values, then 'First values
   --    are returned, and Success is set to False.
   --    If the KeyLength field is not in range, then Success is set
   --    to False.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetKeyInfo (TheCert : in     CertTypes.RawCertificateT;
                         TheKey  :    out PublicKeyInfoT;
                         Success :    out Boolean)
   is
      KeyDict : MsgProc.DictionaryT :=
                      MsgProc.GetDictionaryByKey(
                              Dic => MsgProc.DictionaryT(TheCert),
                              Key => "SubjectPublicKeyInfo");
   begin
      TheKey.AlgorithmID := CryptoTypes.AlgorithmT'Value(
                               MsgProc.GetStringByKey(
                                  Dic => KeyDict,
                                  Key => "AlgoRithmID"));
      TheKey.KeyLength   := CommonTypes.Unsigned32T'Value(
                               MsgProc.GetStringByKey(
                                  Dic => KeyDict,
                                  Key => "KeyLength"));
      TheKey.KeyID       := CommonTypes.Unsigned32T'Value(
                               MsgProc.GetStringByKey(
                                  Dic => KeyDict,
                                  Key => "KeyID"));
      if TheKey.KeyLength <= 128 then
         Success := True;
      else
         Success := False;
         TheKey.KeyLength := CommonTypes.Unsigned32T'First;
      end if;
   exception
      when E : others =>
         Success := False;
         TheKey := (AlgorithmID => CryptoTypes.AlgorithmT'First,
                    KeyLength   => CommonTypes.Unsigned32T'First,
                    KeyID       => CommonTypes.Unsigned32T'First);
   end GetKeyInfo;


   ------------------------------------------------------------------
   -- GetPrivilege
   --
   -- Description:
   --    Attempts to extract the Certificate's Privilege
   --    field.
   --    If there is a problem extracting the values, then 'First values
   --    are returned, and Success is set to False.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetPrivilege(TheCert : in     CertTypes.RawCertificateT;
                          ThePriv :    out PrivilegeT;
                          Success :    out Boolean)
   is
      PrivDict : MsgProc.DictionaryT :=
                    MsgProc.GetDictionaryByKey(
                            Dic => MsgProc.DictionaryT(TheCert),
                            Key => "Privilege");
   begin
      ThePriv.Role  := RoleFrom(
                          RoleValues'Value(
                             MsgProc.GetStringByKey(
                                Dic => PrivDict,
                                Key => "Role")));
      ThePriv.Class := ClassFrom(
                          ClassValues'Value(
                             MsgProc.GetStringByKey(
                                Dic => PrivDict,
                                Key => "Class")));
      Success := True;
   exception
      when E : others =>
         ThePriv := (PrivTypes.PrivilegeT'First,
                     PrivTypes.ClassT'First);
         Success := False;
   end GetPrivilege;


   ------------------------------------------------------------------
   -- GetPrivilege
   --
   -- Description:
   --    Attempts to extract the Certificate's Fingerprint Template
   --    field.
   --    If there is a problem extracting the values, then 'First values
   --    are returned, and Success is set to False.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetTemplate(TheCert  : in     CertTypes.RawCertificateT;
                         Template :    out IandATypes.TemplateT;
                         Success  :    out Boolean)
   is
      TemplateDict : MsgProc.DictionaryT :=
                        MsgProc.GetDictionaryByKey(
                              Dic => MsgProc.DictionaryT(TheCert),
                              Key => "Template");
   begin

      Template.ID  := Ada.Strings.Fixed.Overwrite(
                          IandATypes.TemplateIDT'(others => ' '),
                          1,
                          MsgProc.GetStringByKey(
                             Dic => TemplateDict,
                             Key => "TemplateID"));
      Template.Length := CommonTypes.Unsigned32T'Value(
                          MsgProc.GetStringByKey(
                             Dic => TemplateDict,
                             Key => "TemplateLength"));
      Template.RequiredMaxFAR := IandATypes.FarT'Value(
                                    MsgProc.GetStringByKey(
                                       Dic => TemplateDict,
                                       Key => "RequiredMaxFAR"));
      Success := True;
   exception
      when E : others =>
         Template := IandATypes.NullTemplate;
         Success := False;
   end GetTemplate;


   ------------------------------------------------------------------
   -- OverwriteDigestID
   --
   -- Description:
   --    Overwrites the DigestID in the Crypto string with NewID.
   --    If there is a problem, then the Crypto string remains
   --    unchanged.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure OverwriteDigestID(Crypto : in out String;
                               NewID  : in     CommonTypes.Unsigned32T)
   is
      LocalCrypto : String := Crypto;
      DigestIDKeyEnd,
      DigestIDStart,
      DigestIDEnd : Natural := 0;
   begin
      -- Delete the old DigestID
      DigestIDKeyEnd := Ada.Strings.Fixed.Index(LocalCrypto,
                                                  "DigestID") +
                        9;
      for i in DigestIDKeyEnd..LocalCrypto'Length loop
         if LocalCrypto(i) = ''' then
            if DigestIDStart = 0 then
               DigestIDStart := i + 1;
            else
               DigestIDEnd := i - 1;
               exit;
            end if;
         end if;
      end loop;

      Ada.Strings.Fixed.Delete(LocalCrypto,
                               DigestIDStart,
                               DigestIDEnd);

      -- and insert 'NewID'
      Ada.Strings.Fixed.Insert(LocalCrypto,
                               DigestIDStart,
                               MsgProc.StringFrom32(NewID));
      Crypto := LocalCrypto;
   exception
      when E : others =>
         Null;
   end OverwriteDigestID;


   ------------------------------------------------------------------
   -- ExtractCryptoControlData
   --
   -- Description:
   --    Attempts to extract the Certificate's Fictional Crypto Control
   --    Data, and overwrites the DigestID with 0.
   --    If there is a problem extracting the values, then null
   --    values are returned.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ExtractCryptoControlData(ThePrivCert : CertTypes.RawCertificateT)
   is
      CryptoDict : MsgProc.DictionaryT :=
                      MsgProc.GetDictionaryByKey(
                              Dic => MsgProc.DictionaryT(ThePrivCert),
                              Key => "CryptoControlData");
   begin
      CryptoControlData := Ada.Strings.Fixed.Overwrite(
                                 NullCryptoControl,
                                 1,
                                 String(CryptoDict));

      OverwriteDigestID(CryptoControlData, 0);

   exception
      when E : others =>
         CryptoControlData := NullCryptoControl;
   end ExtractCryptoControlData;


   ------------------------------------------------------------------
   -- Exported Subprograms
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ExtractIDCertData
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   procedure ExtractIDCertData(
                   RawIDCert      : in     CertTypes.RawCertificateT;
                   IDCert         :    out IDCertDataT;
                   ExtractSuccess :    out Boolean
                   )
   is
      LengthOK,
      TypeOK,
      SerialOK,
      AlgOK,
      IssuerOK,
      ValidityOK,
      SubjectOK,
      KeyOK      : Boolean;

      TheCertType     : CommonTypes.Unsigned32T;
      TheSerialNumber : CommonTypes.Unsigned32T;
      TheSigAlgId     : CryptoTypes.AlgorithmT;
      TheIssuer       : CryptoTypes.IssuerT;
      TheValidity     : ValidityT;
      TheSubject      : CryptoTypes.IssuerT;
      TheSubjectPublicKey : PublicKeyInfoT;

   begin
      CheckCertLength(RawIDCert, LengthOK);
      GetCertType (RawIDCert, IDCertType, TheCertType, TypeOK);
      GetSerialNumber (RawIDCert, IDCertType, TheSerialNumber, SerialOK);
      GetSigAlgID (RawIDCert, TheSigAlgID, AlgOK);
      GetName (RawIDCert, IDCertType, False, TheIssuer, IssuerOK);
      GetValidity (RawIDCert, IDCertType, TheValidity, ValidityOK);
      GetName (RawIDCert, IDCertType, True, TheSubject, SubjectOK);
      GetKeyInfo (RawIDCert, TheSubjectPublicKey, KeyOK);

      IDCert := (CertType     => TheCertType,
                 SerialNumber => TheSerialNumber,
                 SigAlgId     => TheSigAlgID,
                 Issuer       => TheIssuer,
                 Validity     => TheValidity,
                 Subject      => TheSubject,
                 SubjectPublicKeyInfo => TheSubjectPublicKey);

      ExtractSuccess := LengthOK and
                        TypeOK and
                        SerialOK and
                        AlgOK and
                        IssuerOK and
                        ValidityOK and
                        SubjectOK and
                        KeyOK;
   end ExtractIDCertData;


   ------------------------------------------------------------------
   -- ExtractPrivCertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (Priv) certificate structure.
   --
   ------------------------------------------------------------------

   procedure ExtractPrivCertData(
                   RawPrivCert    : in     CertTypes.RawCertificateT;
                   PrivCert       :    out PrivCertDataT;
                   ExtractSuccess :    out Boolean
                   )
   is
      LengthOK,
      TypeOK,
      SerialOK,
      AlgOK,
      IssuerOK,
      ValidityOK,
      HolderOK,
      PrivilegeOK     : Boolean;

      TheCertType     : CommonTypes.Unsigned32T;
      TheSerialNumber : CommonTypes.Unsigned32T;
      TheSigAlgId     : CryptoTypes.AlgorithmT;
      TheIssuer       : CryptoTypes.IssuerT;
      TheValidity     : ValidityT;
      TheHolder       : CertTypes.IDT;
      ThePrivilege    : PrivilegeT;

   begin

      CheckCertLength(RawPrivCert, LengthOK);
      GetCertType (RawPrivCert, PrivCertType, TheCertType, TypeOK);
      GetSerialNumber (RawPrivCert, PrivCertType, TheSerialNumber, SerialOK);
      GetSigAlgID (RawPrivCert, TheSigAlgID, AlgOK);
      GetName (RawPrivCert, PrivCertType, False, TheIssuer, IssuerOK);
      GetValidity (RawPrivCert, PrivCertType, TheValidity, ValidityOK);
      GetHolder (RawPrivCert, TheHolder, HolderOK);
      GetPrivilege (RawPrivCert, ThePrivilege, PrivilegeOK);

      PrivCert := (CertType        => TheCertType,
                   SerialNumber    => TheSerialNumber,
                   SigAlgId        => TheSigAlgID,
                   Issuer          => TheIssuer,
                   AttCertValidity => TheValidity,
                   Holder          => TheHolder,
                   Privilege       => ThePrivilege);

      ExtractSuccess := LengthOK and
                        TypeOK and
                        SerialOK and
                        AlgOK and
                        IssuerOK and
                        ValidityOK and
                        HolderOK and
                        PrivilegeOK;

      -- Now we need to extract the CryptoControl data, to insert
      -- into the next created auth cert.
      ExtractCryptoControlData(RawPrivCert);

   end ExtractPrivCertData;


   ------------------------------------------------------------------
   -- ExtractIACertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (I&A) certificate structure.
   --
   ------------------------------------------------------------------

   procedure ExtractIACertData(
                   RawIACert      : in     CertTypes.RawCertificateT;
                   IACert         :    out IACertDataT;
                   ExtractSuccess :    out Boolean
                   )
   is
      LengthOK,
      TypeOK,
      SerialOK,
      AlgOK,
      IssuerOK,
      ValidityOK,
      HolderOK,
      TemplateOK     : Boolean;

      TheCertType     : CommonTypes.Unsigned32T;
      TheSerialNumber : CommonTypes.Unsigned32T;
      TheSigAlgId     : CryptoTypes.AlgorithmT;
      TheIssuer       : CryptoTypes.IssuerT;
      TheValidity     : ValidityT;
      TheHolder       : CertTypes.IDT;
      TheTemplate     : IandATypes.TemplateT;

   begin
      CheckCertLength(RawIACert, LengthOK);
      GetCertType (RawIACert, IACertType, TheCertType, TypeOK);
      GetSerialNumber (RawIACert, IACertType, TheSerialNumber, SerialOK);
      GetSigAlgID (RawIACert, TheSigAlgID, AlgOK);
      GetName (RawIACert, IACertType, False, TheIssuer, IssuerOK);
      GetValidity (RawIACert, IACertType, TheValidity, ValidityOK);
      GetHolder (RawIACert, TheHolder, HolderOK);
      GetTemplate (RawIACert, TheTemplate, TemplateOK);

      IACert := (CertType        => TheCertType,
                 SerialNumber    => TheSerialNumber,
                 SigAlgId        => TheSigAlgID,
                 Issuer          => TheIssuer,
                 AttCertValidity => TheValidity,
                 Holder          => TheHolder,
                 Template        => TheTemplate);

      ExtractSuccess := LengthOK and
                        TypeOK and
                        SerialOK and
                        AlgOK and
                        IssuerOK and
                        ValidityOK and
                        HolderOK and
                        TemplateOK;
   end ExtractIACertData;


   ------------------------------------------------------------------
   -- ExtractAuthCertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (Auth) certificate structure.
   --
   ------------------------------------------------------------------

   procedure ExtractAuthCertData(
                   RawAuthCert    : in     CertTypes.RawCertificateT;
                   AuthCert       :    out AuthCertDataT;
                   ExtractSuccess :    out Boolean
                   )
   is
      LengthOK,
      TypeOK,
      SerialOK,
      AlgOK,
      IssuerOK,
      ValidityOK,
      HolderOK,
      PrivilegeOK     : Boolean;

      TheCertType     : CommonTypes.Unsigned32T;
      TheSerialNumber : CommonTypes.Unsigned32T;
      TheSigAlgId     : CryptoTypes.AlgorithmT;
      TheIssuer       : CryptoTypes.IssuerT;
      TheValidity     : ValidityT;
      TheHolder       : CertTypes.IDT;
      ThePrivilege    : PrivilegeT;

   begin
      CheckCertLength(RawAuthCert, LengthOK);
      GetCertType (RawAuthCert, AuthCertType, TheCertType, TypeOK);
      GetSerialNumber (RawAuthCert, AuthCertType, TheSerialNumber, SerialOK);
      GetSigAlgID (RawAuthCert, TheSigAlgID, AlgOK);
      GetName (RawAuthCert, AuthCertType, False, TheIssuer, IssuerOK);
      GetValidity (RawAuthCert, AuthCertType, TheValidity, ValidityOK);
      GetHolder (RawAuthCert, TheHolder, HolderOK);
      GetPrivilege (RawAuthCert, ThePrivilege, PrivilegeOK);

      AuthCert := (CertType        => TheCertType,
                   SerialNumber    => TheSerialNumber,
                   SigAlgId        => TheSigAlgID,
                   Issuer          => TheIssuer,
                   AttCertValidity => TheValidity,
                   Holder          => TheHolder,
                   Privilege       => ThePrivilege);

      ExtractSuccess := LengthOK and
                        TypeOK and
                        SerialOK and
                        AlgOK and
                        IssuerOK and
                        ValidityOK and
                        HolderOK and
                        PrivilegeOK;

   end ExtractAuthCertData;



   ------------------------------------------------------------------
   -- ObtainRawData
   --
   -- Implementation Notes:
   --    Raw Data is determined by removing the SignatureData from
   --    the CertData dictionary.
   --    The signature may be anywhere in the certificate(!), so need
   --    to find the signature, and delete this along with its key.
   --    If the SignatureData is not found, then return the whole certificate
   --    (it may not have been signed).
   --
   ------------------------------------------------------------------

   procedure ObtainRawData(
                   RawCert       : in     CertTypes.RawCertificateT;
                   RawData       :    out CertTypes.RawDataT;
                   ObtainSuccess :    out Boolean
                   )
   is
      -- Without enclosing braces...
      SigDict      : MsgProc.DictionaryT :=
                        MsgProc.GetDictionaryByKey(
                            Dic => MsgProc.DictionaryT(RawCert),
                            Key => "SignatureData");
      SigDictStart,
      SigKeyStart  : Integer := 0;
      CertData     : MsgProc.DictionaryT :=
                        MsgProc.GetDictionaryByKey(
                            Dic => MsgProc.DictionaryT(RawCert),
                            Key => "CertDataT");

   begin
      SigDictStart := Ada.Strings.Fixed.Index(String(CertData),
                                              String(SigDict));

      SigKeyStart := Ada.Strings.Fixed.Index(String(CertData),
                                             "'SignatureData'");

      if SigKeyStart /= 0 and SigDictStart /= 0 then
         Ada.Strings.Fixed.Delete(String(CertData),
                                  -- From 'SignatureData': ...
                                  SigKeyStart,
                                  -- ... to the enclosing }
                                  SigDictStart + SigDict'Length);
      end if;

      -- If signature data not found, return all of CertData
      RawData.RawData := Ada.Strings.Fixed.Overwrite(
                                CertTypes.NullRawCertificate,
                                1,
                                String(CertData));

      RawData.DataLength := Ada.Strings.Fixed.Trim(
                                      RawData.RawData,
                                      Ada.Strings.Right)'Length;
      ObtainSuccess := True;
   exception
      when E : others =>
         -- return whole certificate
         ObtainSuccess := True;
         RawData := (RawCert,
                     Ada.Strings.Fixed.Trim(
                            RawCert,
                            Ada.Strings.Right)'Length);
   end ObtainRawData;


   ------------------------------------------------------------------
   -- ObtainSignatureData
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   procedure ObtainSignatureData(
                   RawCert       : in     CertTypes.RawCertificateT;
                   SignatureData :    out CertTypes.SignatureT;
                   ObtainSuccess :    out Boolean
                   )
   is
      SigDict : MsgProc.DictionaryT :=
                   MsgProc.GetDictionaryByKey(
                            Dic => MsgProc.DictionaryT(RawCert),
                            Key => "SignatureData");
   begin
      SignatureData := (SigData   => (others => ' '),
                        SigLength => CertTypes.SigDataI'First);

      if SigDict'Length /= 0 then
         Ada.Strings.Fixed.Overwrite(SignatureData.SigData,
                                     1,
                                     String(SigDict));
         if SigDict'Length <= CertTypes.SigDataI'Last then
            SignatureData.SigLength := SigDict'Length;
         else
            SignatureData.SigLength := CertTypes.SigDataI'Last;
         end if;
         ObtainSuccess := True;
      else
         ObtainSuccess := False;
      end if;
   end ObtainSignatureData;



   ------------------------------------------------------------------
   -- ConstructAuthCert
   --
   -- Implementation Notes:
   --    Adds the fictional Crypto dictionary (copied from the Priv Cert)
   --
   ------------------------------------------------------------------

   procedure ConstructAuthCert(
                   AuthCert            : in     AuthCertDataT;
                   UnsignedRawAuthCert :    out CertTypes.RawCertificateT
                   )
   is
      CertTypeString : String :=
                          "'CertType': '" &
                          MsgProc.StringFrom32(AuthCert.CertType) &
                          "', ";
      SerialNoString : String :=
                          "'SerialNumber': '" &
                          MsgProc.StringFrom32(AuthCert.SerialNumber) &
                          "', ";
      SigAlgIDString : String :=
                          "'SigAlgID': '" &
                          CryptoTypes.AlgorithmT'Image(AuthCert.SigAlgID) &
                          "', ";
      IssuerString   : String :=
                          "'Issuer': {'Text': '" &
                          AuthCert.Issuer.Name(1..AuthCert.Issuer.NameLength) &
                          "', 'ID': '" &
                          MsgProc.StringFrom32(CommonTypes.Unsigned32T(AuthCert.Issuer.ID)) &
                          "', 'TextLength': '" &
                          MsgProc.StringFromInt(AuthCert.Issuer.NameLength) &
                          "'}, ";
      ValidityString : String :=
                          "'AttCertValidity': {'NotBefore': {'Minute': '" &
                          MsgProc.StringFrom32(
                             AuthCert.AttCertValidity.NotBefore.Minute) &
                          "', 'Hour': '" &
                          MsgProc.StringFrom32(
                             AuthCert.AttCertValidity.NotBefore.Hour) &
                          "', 'Day': '" &
                          MsgProc.StringFrom32(
                             AuthCert.AttCertValidity.NotBefore.Day) &
                          "', 'Month': '" &
                          MsgProc.StringFrom32(
                             AuthCert.AttCertValidity.NotBefore.Month) &
                          "', 'Year': '" &
                          MsgProc.StringFrom32(
                             AuthCert.AttCertValidity.NotBefore.Year) &
                          "'}, 'NotAfter': {'Minute': '" &
                          MsgProc.StringFrom32(
                             AuthCert.AttCertValidity.NotAfter.Minute) &
                          "', 'Hour': '" &
                          MsgProc.StringFrom32(
                             AuthCert.AttCertValidity.NotAfter.Hour) &
                          "', 'Day': '" &
                          MsgProc.StringFrom32(
                             AuthCert.AttCertValidity.NotAfter.Day) &
                          "', 'Month': '" &
                          MsgProc.StringFrom32(
                             AuthCert.AttCertValidity.NotAfter.Month) &
                          "', 'Year': '" &
                          MsgProc.StringFrom32(
                             AuthCert.AttCertValidity.NotAfter.Year) &
                          "'}}, ";
      HolderString   : String :=
                          "'Holder': {'SerialNumber': '" &
                          MsgProc.StringFrom32(CommonTypes.Unsigned32T(
                             AuthCert.Holder.SerialNumber)) &
                          "', 'Issuer': {'Text': '" &
                          AuthCert.Holder.Issuer.Name(
                                    1..AuthCert.Holder.Issuer.NameLength) &
                          "', 'ID': '" &
                          MsgProc.StringFrom32(CommonTypes.Unsigned32T(
                                    AuthCert.Holder.Issuer.ID)) &
                          "', 'TextLength': '" &
                          MsgProc.StringFromInt(AuthCert.Holder.Issuer.NameLength) &
                          "'}}, ";
      PriviString    : String :=
                          "'Privilege': {'Pad': '??????????', 'Role': '" &
                          MsgProc.StringFrom32(CommonTypes.Unsigned32T(
                            RoleTo(AuthCert.Privilege.Role))) &
                          "', 'Class': '" &
                          MsgProc.StringFrom32(CommonTypes.Unsigned32T(
                            ClassTo(AuthCert.Privilege.Class))) &
                          "'}, ";
      CryptoString   : String :=
                          "'CryptoControlData': {" &
                          Ada.Strings.Fixed.Trim(CryptoControlData, Ada.Strings.
                          Both) &
                          "}, ";
      SigString      : String :=
                          "'SignatureData': {}";

      TheAuthData    : String :=
                          CertTypeString &
                          SerialNoString &
                          SigAlgIDString &
                          IssuerSTring   &
                          ValidityString &
                          HolderString   &
                          PriviString    &
                          CryptoString   &
                          SigString;

      -- Include braces in length, so add 2
      TheAuthLength  : String :=
                          "'CertLength': '" &
                          MsgProc.StringFromInt(TheAuthData'Length + 2) &
                          "', ";

      TheAuthString  : String :=
                          TheAuthLength &
                          "'CertDataT': {" &
                          TheAuthData &
                          "}";


   begin
      UnsignedRawAuthCert := Ada.Strings.Fixed.Overwrite(
                                  CertTypes.NullRawCertificate,
                                  1,
                                  TheAuthString);
   end ConstructAuthCert;



   ------------------------------------------------------------------
   -- AddAuthSignature
   --
   -- Implementation Notes:
   --    Adds the SignatureData to the empty dictionary created in
   --    ConstructAuthCert.
   --    Digest ID in SignatureData is the 'correct' ID - i.e. the ID created
   --    from digesting the unsigned cert. This needs to overwrite the
   --    DigestID in the fictional Crypto dictionary.
   --
   ------------------------------------------------------------------

   procedure AddAuthSignature(
                   UnsignedRawAuthCert : in     CertTypes.RawCertificateT;
                   SignatureData       : in     CertTypes.SignatureT;
                   SignedRawAuthCert   :    out CertTypes.RawCertificateT)
   is
      NewID : CommonTypes.Unsigned32T;

      SigDataString  : String := SignatureData.SigData(
                                    1..SignatureData.SigLength);
      SigDictStart   : Natural;

      CertLengthKey  : String := "'CertLength':";

      LengthKeyStart : Natural;
      LengthValStart,
      LengthValEnd   : Natural := 0;

   begin
      SignedRawAuthCert := UnsignedRawAuthCert;

      -- Attempt to replace the old DigestID with the new one
      begin
         NewID := CommonTypes.Unsigned32T'Value(
                     MsgProc.GetStringByKey(
                        MsgProc.DictionaryT(SigDataString),
                        "DigestID"));
         OverwriteDigestID(SignedRawAuthCert, NewID);
      exception
         when E : others =>
            Null;
      end;

      -- Find and overwrite the blank signature
      SigDictStart := Ada.Strings.Fixed.Index(SignedRawAuthCert, "{}");

      if SigDictStart /= 0 then
         Ada.Strings.Fixed.Insert(SignedRawAuthCert,
                                  SigDictStart + 1,
                                  SigDataString,
                                  Ada.Strings.Right);
      end if; -- else would only occur if UnsignedRawAuthCert is
              -- not that contructed by ConstructAuthCert

      -- Determine the new CertLength, and overwrite old one
      declare
         TheCertData  : MsgProc.DictionaryT :=
                           MsgProc.GetDictionaryByKey(
                              MsgProc.DictionaryT(SignedRawAuthCert),
                              "CertDataT");

      begin
         LengthKeyStart := Ada.Strings.Fixed.Index(SignedRawAuthCert,
                                                   CertLengthKey);

         for i in CertTypes.RawCertificateI range
            LengthKeyStart + CertLengthKey'Length-1 .. CertTypes.RawCertificateI'Last loop
            if SignedRawAuthCert(i) = ''' then
               if LengthValStart = 0 then
                  LengthValStart := i + 1;
               else
                  LengthValEnd := i - 1;
                  exit;
               end if;
            end if;
         end loop;

         -- Include braces in length, so add 2
         Ada.Strings.Fixed.Replace_Slice(SignedRawAuthCert,
                                        LengthValStart,
                                        LengthValEnd,
                                        MsgProc.StringFromInt(TheCertData'Length + 2),
                                        Ada.Strings.Right);
      end;

   end AddAuthSignature;

end CertProc;
