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
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with SPARK_IO,
     Ada.Strings,
     Ada.Strings.Fixed,
     CommonTypes,
     CryptoTypes,
     MsgProc;

use type SPARK_IO.File_Status;
use type CryptoTypes.IssuerIDT;
use type CommonTypes.Unsigned32T;

package body Crypto
  with SPARK_Mode => Off  --  exception handlers
is

   -- State.

   -- NextHandle acts as a pointer to the next position in the keystore.
   -- Initialized to the maximum possible value, before being formally
   -- initialized by the Initialize procedure.
   subtype HandleT is CommonTypes.Unsigned32T range 1..100;
   NextHandle : HandleT := 100;

   -- IsInit keeps track of the state of the cryptoki library.
   IsInit: Boolean := False;

   -- DigestState keeps track of the state of a digest operation
   -- Holds the certificate read so far, and the current index
   -- (at which to write the next chunk).
   type DigestStateT is record
      Initialized : Boolean;
      RawCert     : CertTypes.RawCertificateT;
      CertIndex   : CertTypes.RawCertificateI;
   end record;

   NullDigestState : constant DigestStateT :=
     (Initialized => False,
      RawCert     => (others => ASCII.nul),
      CertIndex   => CertTypes.RawCertificateI'First);

   DigestState : DigestStateT := NullDigestState;

   -- FindState keeps track of the state of a find operation
   type FindStateT is record
      Initialized  : Boolean;
      FindTemplate : KeyTemplateT;
   end record;

   NullKeyTemplate : constant KeyTemplateT :=
     (AttrMask  => 15,
      Owner     => CryptoTypes.IssuerT'
        (ID         => 0,
         NameLength => 0,
         Name       => CryptoTypes.NameT'(others => ' ')),
      KeyID     => 0,
      KeyLength => 0,
      IsPublic  => True,
      Padding   => KeyPaddingT'(others => 0));

   NullFindState : constant FindStateT :=
     (Initialized  => False,
      FindTemplate => NullKeyTemplate);

   FindState : FindStateT := NullFindState;

   -- KeyStore is the internal version of the keystore file. Initialized
   -- by the Initialize operation, and updated in line with any additions
   -- to the file.
   type T is array (HandleT) of KeyTemplateT;
   NullKeyStore : constant T := T'(others => NullKeyTemplate);
   KeyStore : T := NullKeyStore;

   ------------
   -- Constants
   ------------

   -- The KeyStore file looks like:
   -------
   -- Owner.ID:123
   -- Owner.Text:David Painter
   -- KeyID:20021977
   -- KeyLength:128
   -- IsPublic:Y
   --
   -- Owner.ID:456
   -- ...
   -------
   -- a Title is the Attribute name followed by a colon e.g. "Owner.ID:"
   subtype OwnerIDIndexT is Positive range 1..9;
   subtype OwnerIDT is String(OwnerIDIndexT);

   subtype OwnerTextIndexT is Positive range 1..11;
   subtype OwnerTextT is String(OwnerTextIndexT);

   subtype KeyIDIndexT is Positive range 1..6;
   subtype KeyIDT is String(KeyIDIndexT);

   subtype KeyLengthIndexT is Positive range 1..10;
   subtype KeyLengthT is String(KeyLengthIndexT);

   subtype IsPublicIndexT is Positive range 1..9;
   subtype IsPublicT is String(IsPublicIndexT);

   OwnerIDTitle   : constant OwnerIDT   := "Owner.ID:";
   OwnerTextTitle : constant OwnerTextT := "Owner.Text:";
   KeyIDTitle     : constant KeyIDT     := "KeyID:";
   KeyLengthTitle : constant KeyLengthT := "KeyLength:";
   IsPublicTitle  : constant IsPublicT  := "IsPublic:";


   -- TypeOf returns the operations that a mechanism can be used for.
   type MechanismTypeT is (Signing, Digesting, Combined);
   type MechanismToTypeT is array (CryptoTypes.AlgorithmT)
                             of MechanismTypeT;

   TypeOf : constant MechanismToTypeT :=
     (CryptoTypes.RSA           => Signing,
      CryptoTypes.MD2           => Digesting,
      CryptoTypes.MD5           => Digesting,
      CryptoTypes.SHA_1         => Digesting,
      CryptoTypes.RIPEMD128     => Digesting,
      CryptoTypes.RIPEMD160     => Digesting,
      CryptoTypes.MD2_RSA       => Combined,
      CryptoTypes.MD5_RSA       => Combined,
      CryptoTypes.SHA1_RSA      => Combined,
      CryptoTypes.RIPEMD128_RSA => Combined,
      CryptoTypes.RIPEMD160_RSA => Combined);

   ------------------------------------------------------------------
   -- Local subprograms
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- Create,OpenForAppending,OpenForReading,Close
   --
   -- Description:
   --    Procedures for controlling the state of the keystore file.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Create
     (FileHandle :    out SPARK_IO.File_Type;
      Created    :    out Boolean)
   is
      Status : SPARK_IO.File_Status;
   begin
      SPARK_IO.Create(File => FileHandle,
                      Name_Of_File => "./System/keystore",
                      Form_Of_File => "",
                      Status => Status);
      Created := (Status = SPARK_IO.OK);
   end Create;

   procedure OpenForAppending (FileHandle :    out SPARK_IO.File_Type;
                               Open       :    out Boolean)
   is
      Status : SPARK_IO.File_Status;
   begin
      SPARK_IO.Open(File => FileHandle,
                    Mode_Of_File => SPARK_IO.Append_File,
                    Name_Of_File => "./System/keystore",
                    Form_Of_File => "",
                    Status       => Status);
      Open := (Status = SPARK_IO.OK);
   end OpenForAppending;

   procedure OpenForReading (FileHandle :    out SPARK_IO.File_Type;
                             Open       :    out Boolean)
   is
      Status : SPARK_IO.File_Status;
   begin
      SPARK_IO.Open(File => FileHandle,
                    Mode_Of_File => SPARK_IO.In_File,
                    Name_Of_File => "./System/keystore",
                    Form_Of_File => "",
                    Status       => Status);
      Open := (Status = SPARK_IO.OK);
   end OpenForReading;

   procedure Close (FileHandle : in     SPARK_IO.File_Type;
                    Closed     :    out Boolean)
   is
      Status : SPARK_IO.File_Status;
   begin
      SPARK_IO.Close(File => FileHandle,
                     Status => Status);
      Closed := (Status = SPARK_IO.OK);
   end Close;

   ------------------------------------------------------------------
   -- ToString
   --
   -- Description:
   --    Converts a character to a string
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function ToString(Ch : Character) return String is
   begin
      return Ada.Strings.Fixed."*"(1,Ch);
   end ToString;

   ------------------------------------------------------------------
   -- Exported subprograms
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- Initialize
   --
   -- Implementation Notes:
   --    Attempts to open the "keystore" file. If this fails, then
   --    assumes the store has not been previously created, and
   --    creates a new one. Fills in the local KeyStore state.
   --
   ------------------------------------------------------------------
   procedure Initialize(ReturnValue : out ReturnValueT) is
      Keys         : SPARK_IO.File_Type;
      Open, Closed : Boolean;
      Created      : Boolean := False;
      ReadOK       : Boolean := True;

      ------------------------------------------------------------------
      -- UpdateLocalStore
      --
      -- Description:
      --    Initializes the local copy of the keystore from the file.
      --    Stops as soon as there is a problem reading from the file.
      --
      -- Implementation Notes:
      --    None.
      --
      ------------------------------------------------------------------
      procedure UpdateLocalStore is
         CurrentHandle : HandleT := HandleT'First;


         ------------------------------------------------------------------
         -- Read'Attr'
         --
         -- Description:
         --    Attempts to read the 'Attr' from the file. If the correct
         --    title is not found, or the value is not found,
         --    the global ReadOK is set to False.
         --
         -- Implementation Notes:
         --    ReadOwnerID searches for the next Owner ID, all other reads
         --    are done blind - that is they just read the next line.
         --
         ------------------------------------------------------------------
         procedure ReadOwnerID is
            IDTitle  : OwnerIDT;
            IDString : String (1 .. 20) := (others => ' ');
            IDLength : Natural;
            Index    : Integer;
         begin
            -- Find the start of the next Key.
            while not SPARK_IO.End_Of_File (File => Keys) loop
               SPARK_IO.Get_String (File => Keys,
                                    Item => IDTitle,
                                    Stop => Index);

               exit when Index = OwnerIDIndexT'Last and then
                         IDTitle = OwnerIDTitle;
            end loop;

            if not SPARK_IO.End_Of_File (File => Keys) then

               -- Found the Owner ID title; attempt to read the ID.
               SPARK_IO.Get_Line (File => Keys,
                                  Item => IDString,
                                  Stop => IDLength);

               KeyStore (CurrentHandle).Owner.ID :=
                       CryptoTypes.IssuerIDT'Value (IDString);

            end if; -- Do nothing if end of file

         exception
            when E : others =>
               -- What we read was not a 32-bit integer - fail
               ReadOK := False;
         end ReadOwnerID;

         procedure ReadOwnerText is
            TextTitle : OwnerTextT;
            Count : CryptoTypes.NameCountT := 0;
            Name : CryptoTypes.NameT := (others => ' ');
            Index : Integer;

         begin
            SPARK_IO.Get_String(File => Keys,
                                Item => TextTitle,
                                Stop => Index);

            if Index = OwnerTextIndexT'Last and then
               TextTitle = OwnerTextTitle then

               SPARK_IO.Get_Line (File => Keys,
                                  Item => Name,
                                  Stop => Count);

               KeyStore (CurrentHandle).Owner.Name := Name;
               KeyStore (CurrentHandle).Owner.NameLength := Count;
            else
               ReadOK := False;
            end if;
         end ReadOwnerText;

         procedure ReadKeyID is
            IDTitle  : KeyIDT;
            IDString : String (1 .. 20) := (others => ' ');
            IDLength : Natural;
            Index    : Integer;

         begin
            SPARK_IO.Get_String(File => Keys,
                                Item => IDTitle,
                                Stop => Index);

            if Index = KeyIDIndexT'Last and then
               IDTitle = KeyIDTitle then

               -- Found the Key ID title, attempt to read the ID.
               SPARK_IO.Get_Line(File => Keys,
                                 Item => IDString,
                                 Stop => IDLength);

               KeyStore(CurrentHandle).KeyID :=
                       CommonTypes.Unsigned32T'Value(IDString);

            else

               ReadOK := False;

            end if;
         exception
            when E : others =>
               -- What we read was not a 32-bit integer - fail
               ReadOK := False;
         end ReadKeyID;

         procedure ReadKeyLength is
            LengthTitle  : KeyLengthT;
            LenString    : String(1..20) := (others => ' ');
            LenStrLength : Natural;
            Index        : Integer;

         begin
            SPARK_IO.Get_String(File => Keys,
                                Item => LengthTitle,
                                Stop => Index);
            if Index = KeyLengthIndexT'Last and then
               LengthTitle = KeyLengthTitle then

               SPARK_IO.Get_Line(File => Keys,
                                 Item => LenString,
                                 Stop => LenStrLength);

               KeyStore(CurrentHandle).KeyLength :=
                       CommonTypes.Unsigned32T'Value(LenString);

            else
               ReadOK := False;
            end if;
         exception
            when E : others =>
               -- What we read was not a 32-bit integer - fail
               ReadOK := False;
         end ReadKeyLength;

         procedure ReadIsPublic is
            PublicTitle : IsPublicT;
            TheChar  : Character;
            Index    : Integer;

         begin
            SPARK_IO.Get_String(File => Keys,
                                Item => PublicTitle,
                                Stop => Index);

            if Index = IsPublicIndexT'Last and then
               PublicTitle = IsPublicTitle then

               -- Found the Is Public title, attempt to read the Y/N char.
               SPARK_IO.Get_Char(File  => Keys,
                                 Item  => TheChar);

               if TheChar = 'Y' or
                  TheChar = 'y' then

                  KeyStore(CurrentHandle).IsPublic := True;

               elsif TheChar = 'N' or
                     TheChar = 'n' then

                  KeyStore(CurrentHandle).IsPublic := False;

               else
                  ReadOK := False;
               end if;

               SPARK_IO.Skip_Line(File    => Keys, Spacing => 1);
            else
               ReadOK := False;
            end if;
         end ReadIsPublic;

      begin -- UpdateLocalStore
         loop
            ReadOwnerID;
            exit when SPARK_IO.End_Of_File(File => Keys);

            if ReadOK then
               ReadOwnerText;
            end if;

            if ReadOK then
               ReadKeyID;
            end if;

            if ReadOK then
               ReadKeyLength;
            end if;

            if ReadOK then
               ReadIsPublic;
            end if;

            exit when not ReadOK;
            CurrentHandle := CurrentHandle + 1;
         end loop;

         NextHandle := CurrentHandle;
      end UpdateLocalStore;

   begin -- Initialize
      NextHandle := 1;
      OpenForReading (FileHandle => Keys, Open => Open);

      if not Open then
         Create (FileHandle => Keys, Created => Created);
      else
         UpdateLocalStore;
      end if;

      Close (FileHandle => Keys, Closed => Closed);

      if ((Open and ReadOK) or Created) and Closed then
         if not IsInit then
            ReturnValue := Ok;
            IsInit := True;
         else
            ReturnValue := CryptokiAlreadyInitialized;
         end if;
      else
         ReturnValue := FunctionFailed;
         IsInit := False;
      end if;

   exception
      when E : others =>
         ReturnValue := FunctionFailed;
         IsInit := False;
   end Initialize;

   ------------------------------------------------------------------
   -- Finalize
   --
   -- Implementation Notes:
   --    Don't need to do anything here - the file is always closed
   --    after reading or appending.
   --
   ------------------------------------------------------------------
   procedure Finalize (ReturnValue : out ReturnValueT) is
   begin
      ReturnValue := Ok;
      IsInit := False;
   end Finalize;

   ------------------------------------------------------------------
   -- CreateObject
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure CreateObject (Template     : in     KeyTemplateT;
                           ObjectHandle :    out CommonTypes.Unsigned32T;
                           ReturnValue  :    out ReturnValueT)
   is
      Keys : SPARK_IO.File_Type;
      Open, Closed : Boolean;

      ------------------------------------------------------------------
      -- Add'Attr'
      --
      -- Description:
      --    Writes the Attr title and value to the keystore file
      --
      -- Implementation Notes:
      --    The file should already be open for appending
      --
      ------------------------------------------------------------------
      procedure AddOwner is
      begin
         SPARK_IO.Put_String(File => Keys,
                             Item => OwnerIDTitle,
                             Stop => 0);

         SPARK_IO.Put_String(File => Keys,
                             Item => MsgProc.StringFrom32(
                                        CommonTypes.Unsigned32T(
                                           Template.Owner.Id)),
                             Stop => 0);

         SPARK_IO.New_Line(File => Keys,
                           Spacing => 1);

         SPARK_IO.Put_String(File => Keys,
                             Item => OwnerTextTitle,
                             Stop => 0);

         SPARK_IO.Put_String(File => Keys,
                             Item => Template.Owner.Name,
                             Stop => Integer(Template.Owner.NameLength));

         SPARK_IO.New_Line(File => Keys,
                           Spacing => 1);
      end AddOwner;

      procedure AddKey is
      begin
         SPARK_IO.Put_String(File => Keys,
                             Item => KeyIDTitle,
                             Stop => 0);

         SPARK_IO.Put_String(File => Keys,
                             Item => MsgProc.StringFrom32(
                                        Template.KeyId),
                             Stop => 0);

         SPARK_IO.New_Line(File => Keys,
                           Spacing => 1);

         SPARK_IO.Put_String(File => Keys,
                             Item => KeyLengthTitle,
                             Stop => 0);

         SPARK_IO.Put_String(File => Keys,
                             Item => MsgProc.StringFrom32(
                                        Template.KeyLength),
                             Stop => 0);

         SPARK_IO.New_Line(File => Keys,
                           Spacing => 1);
      end AddKey;

      procedure AddIsPublic is
      begin
         SPARK_IO.Put_String(File => Keys,
                             Item => IsPublicTitle,
                             Stop => 0);

         if Template.IsPublic then
            SPARK_IO.Put_String(File => Keys,
                                Item => "Y",
                                Stop => 0);
         else
            SPARK_IO.Put_String(File => Keys,
                                Item => "N",
                                Stop => 0);
         end if;

         SPARK_IO.New_Line(File => Keys,
                           Spacing => 1);
      end AddIsPublic;

   begin -- CreateObject

      ObjectHandle := 0;

      if NextHandle = HandleT'Last then
         -- Key store is full
         ReturnValue := FunctionFailed;
      else
         -- Add key to store
         OpenForAppending(FileHandle => Keys, Open => Open);

         if Open then
            AddOwner;
            AddKey;
            AddIsPublic;
            ObjectHandle := NextHandle;
         end if;

         Close (FileHandle => Keys, Closed => Closed);

         if Open and Closed then
            ReturnValue := Ok;
            -- Success, so update local store
            KeyStore (NextHandle) := Template;
            NextHandle := NextHandle + 1;
         else
            ReturnValue := FunctionFailed;
         end if;
      end if;
   end CreateObject;

   ------------------------------------------------------------------
   -- FindObjectsInit
   --
   -- Implementation Notes:
   --    Updates FindState
   --
   ------------------------------------------------------------------
   procedure FindObjectsInit
     (Template    : in     KeyTemplateT;
      ReturnValue :    out ReturnValueT) is
   begin
      if not IsInit then
         ReturnValue := CryptokiNotInitialized;
      elsif FindState.Initialized or
            DigestState.Initialized then
         ReturnValue := OperationActive;
      else
         FindState := FindStateT'(Initialized  => True,
                                  FindTemplate => Template);
         ReturnValue := Ok;
      end if;

   end FindObjectsInit;

   ------------------------------------------------------------------
   -- FindObjects
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure FindObjects (HandleCount   : in out CommonTypes.Unsigned32T;
                          ObjectHandles :    out HandleArrayT;
                          ReturnValue   :    out ReturnValueT)
   is
      MatchCount : HandleCountT := 0;

      ------------------------------------------------------------------
      -- 'Attr'Match
      --
      -- Description:
      --    Returns true if the Attr for the key handle matches that
      --    in the template, or the attr is not defined in the template.
      --
      -- Implementation Notes:
      --    None.
      --
      ------------------------------------------------------------------
      function OwnerMatch (Idx : HandleT) return Boolean
      is
      begin
        return (OwnerMask and
                FindState.FindTemplate.AttrMask) = MaskT(0) or else
           KeyStore(Idx).Owner.Id = FindState.FindTemplate.Owner.Id;
      end OwnerMatch;

      function KeyIDMatch (Idx : HandleT) return Boolean
      is
      begin
        return (KeyIDMask and
                FindState.FindTemplate.AttrMask) = MaskT(0) or else
           KeyStore(Idx).KeyId = FindState.FindTemplate.KeyId;
      end KeyIDMatch;

      function KeyLengthMatch (Idx : HandleT) return Boolean
      is
      begin
        return (KeyLengthMask and
                FindState.FindTemplate.AttrMask) = MaskT(0) or else
           KeyStore(Idx).KeyLength = FindState.FindTemplate.KeyLength;
      end KeyLengthMatch;

      function IsPublicMatch (Idx : HandleT) return Boolean
      is
      begin
        return (IsPublicMask and
                FindState.FindTemplate.AttrMask) = MaskT(0) or else
           KeyStore(Idx).IsPublic = FindState.FindTemplate.IsPublic;
      end IsPublicMatch;

   begin -- FindObjects

     ObjectHandles := HandleArrayT'(others => 0);

     if not IsInit then
        ReturnValue := CryptokiNotInitialized;
        -- Find operation has gone wrong - clear the state
        FindState   := NullFindState;
     elsif not FindState.Initialized then
        ReturnValue := OperationNotInitialized;
        -- Find operation has gone wrong - clear the state
        FindState   := NullFindState;
     else

        -- Search on Owner first
        for i in HandleT loop
           exit when i = NextHandle;

           if OwnerMatch(Idx => i) and
              KeyIDMatch(Idx => i) and
              KeyLengthMatch(Idx => i) and
              IsPublicMatch(Idx => i) then

              if MatchCount < HandleCountT'Last then
                 MatchCount := MatchCount + 1;
              end if;

              if CommonTypes.Unsigned32T(MatchCount) <= HandleCount then
                 ObjectHandles(MatchCount) := i;
              end if;

           end if;
        end loop;

        HandleCount := CommonTypes.Unsigned32T(MatchCount);
        ReturnValue := Ok;

      end if;
   end FindObjects;

   ------------------------------------------------------------------
   -- FindObjectsFinal
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure FindObjectsFinal (ReturnValue : out ReturnValueT)
   is
   begin
     if not IsInit then
        ReturnValue := CryptokiNotInitialized;
     elsif not FindState.Initialized then
        ReturnValue := OperationNotInitialized;
     else
        ReturnValue := Ok;
     end if;
     -- Clear the FindState regardless
     FindState := NullFindState;
   end FindObjectsFinal;

   ------------------------------------------------------------------
   -- DigestInit
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure DigestInit (Mechanism   : in     CryptoTypes.AlgorithmT;
                         ReturnValue :    out ReturnValueT)
   is
   begin
      if not IsInit then
         ReturnValue := CryptokiNotInitialized;
      elsif FindState.Initialized or
            DigestState.Initialized then
         ReturnValue := OperationActive;
      elsif TypeOf(Mechanism) /= Combined and
               TypeOf(Mechanism) /= Digesting then
            ReturnValue := MechanismInvalid;
      else
         DigestState.Initialized := True;
         ReturnValue := Ok;
      end if;
   end DigestInit;

   ------------------------------------------------------------------
   -- DigestUpdate
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure DigestUpdate (DataBlock   : in     HundredByteArrayT;
                           ByteCount   : in     CommonTypes.Unsigned32T;
                           ReturnValue :    out ReturnValueT)
   is

      ------------------------------------------------------------------
      -- CalcDigestUpdateReturn
      --
      -- Description:
      --    If the entire certificate has been read, then return
      --    the 'DigestUpdateReturn' value from the certificate.
      --    Otherwise return 'Ok'
      --
      -- Implementation Notes:
      --    Use the CertLength data in the certificate to determine
      --    whether all of the certificate has been read.
      --
      ------------------------------------------------------------------
      function CalcDigestUpdateReturn return ReturnValueT
      is
         ReturnValue : ReturnValueT := Ok;
      begin

         if not IsInit then
            ReturnValue := CryptokiNotInitialized;
         elsif not DigestState.Initialized then
            ReturnValue := OperationNotInitialized;
         else

            declare
               CryptoDict : MsgProc.DictionaryT :=
                      MsgProc.GetDictionaryByKey(
                         Dic => MsgProc.DictionaryT(DigestState.RawCert),
                         Key => "CryptoControlData");
            begin
               if CryptoDict'Length /= 0 then
                  -- all of the certificate has been read
                  ReturnValue := ReturnValueT'Value(
                                    MsgProc.GetStringByKey(
                                       Dic => CryptoDict,
                                       Key => "DigestUpdateReturn"));
               end if;
            end;
         end if;
         return ReturnValue;
      exception
         -- exception caused by unknown value for DigestUpdateReturn.
         when E : others =>
            return FunctionFailed;
      end CalcDigestUpdateReturn;

   begin
     if DigestState.Initialized then
        DigestState.RawCert(DigestState.CertIndex..
                            DigestState.CertIndex +
                            CertTypes.RawCertificateI(ByteCount) - 1) :=
              DataBlock(1..Integer(ByteCount));
        if DigestState.CertIndex <= CertTypes.RawCertificateI'Last -
                         CertTypes.RawCertificateI(ByteCount) then
        DigestState.CertIndex := DigestState.CertIndex +
                                 CertTypes.RawCertificateI(ByteCount);
        else
           DigestState.CertIndex := CertTypes.RawCertificateI'Last;
        end if;
     end if;
     ReturnValue := CalcDigestUpdateReturn;

     if ReturnValue /= Ok then
        -- The digest has gone wrong, clear the state
        DigestState := NullDigestState;
     end if;
   end DigestUpdate;


   ------------------------------------------------------------------
   -- DigestFinal
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure DigestFinal (Digest       : out DigestT;
                          DigestLength : out CommonTypes.Unsigned32T;
                          ReturnValue  : out ReturnValueT)
   is
      CertDict  : MsgProc.DictionaryT :=
        MsgProc.DictionaryT(DigestState.RawCert);

      ------------------------------------------------------------------
      -- CalcDigest
      --
      -- Description:
      --    Extracts the digest 'dictionary' from the certificate and
      --    returns this digest. If the DigestID is 0 then a new ID is
      --    calculated.
      --
      -- Implementation Notes:
      --    None.
      --
      ------------------------------------------------------------------
      function CalcDigest return DigestT
      is
         TheDigest : DigestT;
         DigestDict : MsgProc.DictionaryT :=
                   MsgProc.GetDictionaryByKey(Dic => CertDict,
                                              Key => "Digest");

      begin
         TheDigest.DigestID := CommonTypes.Unsigned32T'Value(
                            MsgProc.GetStringByKey(Dic => DigestDict,
                                                   Key => "DigestID"));

         TheDigest.SignReturn := ReturnValueT'Value(
                            MsgProc.GetStringByKey(Dic => DigestDict,
                                                   Key => "SignReturn"));

         TheDigest.VerifyReturn := ReturnValueT'Value(
                            MsgProc.GetStringByKey(Dic => DigestDict,
                                                   Key => "VerifyReturn"));

         if TheDigest.DigestID = 0 then
            -- Need to calculate a new digest ID from the certificate
            for i in Positive range 1..CertDict'Length loop
               TheDigest.DigestID :=
                     (CommonTypes.Unsigned32T(TheDigest.DigestID) +
                      CommonTypes.Unsigned32T(i * Character'Pos(CertDict(i)))
                     ) mod CommonTypes.Unsigned32T'Last;
            end loop;
         end if;

         return TheDigest;
      exception
         -- problem extracting the digest - ensure any signing or
         -- verifying of this digest will fail.
         when E : others =>
            return DigestT'(
                      DigestID     => 0,
                      SignReturn   => FunctionFailed,
                      VerifyReturn => FunctionFailed,
                      Pad          => (others => 0));
      end CalcDigest;

      ------------------------------------------------------------------
      -- CalcDigestLength
      --
      -- Description:
      --    Extracts the DigestLength from the certificate and
      --    returns this.
      --
      -- Implementation Notes:
      --    None.
      --
      ------------------------------------------------------------------
      function CalcDigestLength return CommonTypes.Unsigned32T
      is
      begin

         return CommonTypes.Unsigned32T'Value(
                           MsgProc.GetStringByKey(
                              Dic => CertDict,
                              Key => "DigestLength"));
      exception
         -- return invalid length
         when E : others =>
            return CommonTypes.Unsigned32T'Last;
      end CalcDigestLength;

      ------------------------------------------------------------------
      -- CalcDigestFinalReturn
      --
      -- Description:
      --    Determines the ReturnValue to return from this digest op.
      --
      -- Implementation Notes:
      --    None.
      --
      ------------------------------------------------------------------
      function CalcDigestFinalReturn return ReturnValueT
      is
         ReturnValue : ReturnValueT;
      begin

         if not IsInit then
            ReturnValue := CryptokiNotInitialized;
         elsif not DigestState.Initialized then
            ReturnValue := OperationNotInitialized;
         elsif DigestLength > 32 then
            ReturnValue := DataLenRange;
         else
            ReturnValue := ReturnValueT'Value(
                        MsgProc.GetStringByKey(
                           Dic => CertDict,
                           Key => "DigestFinalReturn"));
         end if;
         return ReturnValue;
      exception
         when E : others =>
            return FunctionFailed;
      end CalcDigestFinalReturn;

   begin -- DigestFinal
     Digest       := CalcDigest;
     DigestLength := CalcDigestLength;
     ReturnValue  := CalcDigestFinalReturn;
     -- Clear the digest state
     DigestState  := NullDigestState;
   end DigestFinal;

   ------------------------------------------------------------------
   -- Sign
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Sign (Mechanism    : in     CryptoTypes.AlgorithmT;
                   KeyHandle    : in     CommonTypes.Unsigned32T;
                   Digest       : in     DigestT;
                   Signature    :    out CertTypes.SignatureT;
                   ReturnValue  :    out ReturnValueT)
   is

      function CreateSignatureFrom
        (AlgorithmID : CryptoTypes.AlgorithmT;
         Siglength   : CommonTypes.Unsigned32T;
         KeyID       : CommonTypes.Unsigned32T;
         DigestID    : CommonTypes.Unsigned32T)
        return CertTypes.SignatureT
      is
         TrimKeyID : String := Ada.Strings.Fixed.Trim(
                                  MsgProc.StringFrom32(KeyID),
                                  Ada.Strings.Both);
         TrimDigID : String := Ada.Strings.Fixed.Trim(
                                  MsgProc.StringFrom32(DigestID),
                                  Ada.Strings.Both);
         TrimLength : String := Ada.Strings.Fixed.Trim(
                                  MsgProc.StringFrom32(SigLength),
                                  Ada.Strings.Both);
         SigString : String := "'AlgoRithmID': '" &
                               CryptoTypes.AlgorithmT'Image(AlgorithmID) &
                               "', 'SigLength': '" &
                               TrimLength &
                               "', 'Signature': {'KeyID': '" &
                               TrimKeyID &
                               "', 'DigestID': '" &
                               TrimDigID &
                               "'}";
         TheSignature : CertTypes.SignatureT;
      begin
         if SigString'Length > CertTypes.MaxSigDataLength then
            TheSignature := ((others => ' '),
                             1);
         else
            TheSignature :=
                (SigData   => Ada.Strings.Fixed.Overwrite(
                                 CertTypes.SigDataT'(others => ' '),
                                 1,
                                 SigString),
                 SigLength => SigString'Length);
         end if;
         return TheSignature;
      end CreateSignatureFrom;

   begin -- Sign
      Signature := CertTypes.SignatureT'(
               SigData   => (others => ' '),
               SigLength => 1);

      if not IsInit then
         ReturnValue := CryptokiNotInitialized;
      elsif FindState.Initialized or
            DigestState.Initialized then
         ReturnValue := OperationActive;
      elsif TypeOf(Mechanism) /= Signing and
               TypeOf(Mechanism) /= Combined then
            ReturnValue := MechanismInvalid;
      else
         Signature := CreateSignatureFrom(
               AlgorithmID => Mechanism,
               Siglength   => KeyStore(KeyHandle).KeyLength,
               KeyID       => KeyStore(KeyHandle).KeyID,
               DigestID    => Digest.DigestID
               );
         ReturnValue := Digest.SignReturn;
      end if;
   end Sign;

   ------------------------------------------------------------------
   -- Verify
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Verify (Mechanism    : in     CryptoTypes.AlgorithmT;
                     KeyHandle    : in     CommonTypes.Unsigned32T;
                     Digest       : in     DigestT;
                     Signature    : in     CertTypes.SignatureT;
                     ReturnValue  :    out ReturnValueT)
   is

      function TheKeyID (Signature : CertTypes.SignatureT)
                        return CommonTypes.Unsigned32T
      is
      begin
         return CommonTypes.Unsigned32T'Value(
                   MsgProc.GetStringByKey(
                          Dic => MsgProc.DictionaryT(Signature.SigData),
                          Key => "KeyID"));
      exception
         when E : others =>
            return CommonTypes.Unsigned32T'Last;
      end TheKeyID;

      function TheDigestID(Signature : CertTypes.SignatureT)
            return CommonTypes.Unsigned32T
      is
      begin
         return CommonTypes.Unsigned32T'Value(
                   MsgProc.GetStringByKey(
                          Dic => MsgProc.DictionaryT(Signature.SigData),
                          Key => "DigestID"));
      exception
         when E : others =>
            return CommonTypes.Unsigned32T'Last;
      end TheDigestID;

      function TheSigLength(Signature : CertTypes.SignatureT)
            return CommonTypes.Unsigned32T
      is
      begin
         return CommonTypes.Unsigned32T'Value(
                   MsgProc.GetStringByKey(
                          Dic => MsgProc.DictionaryT(Signature.SigData),
                          Key => "SigLength"));
      exception
         when E : others =>
            return CommonTypes.Unsigned32T'Last;
      end TheSigLength;

   begin -- Verify
      if not IsInit then
         ReturnValue := CryptokiNotInitialized;
      elsif FindState.Initialized or
            DigestState.Initialized then
         ReturnValue := OperationActive;
      elsif TypeOf(Mechanism) /= Signing and
               TypeOf(Mechanism) /= Combined then
         ReturnValue := MechanismInvalid;
      elsif KeyStore(KeyHandle).KeyID /= TheKeyID(Signature) or
               Digest.DigestID /= TheDigestID(Signature) then
         ReturnValue := SignatureInvalid;
      elsif TheSigLength(Signature) >
               KeyStore(KeyHandle).KeyLength then
         ReturnValue := SignatureLenRange;
      else
         ReturnValue := Digest.VerifyReturn;
      end if;
   end Verify;

   ------------------------------------------------------------------
   -- GetAttributeValue
   --
   -- Description:
   --    Extracts attribute data from the object pointed to by KeyHandle.
   --
   ------------------------------------------------------------------
   procedure GetAttributeValue (KeyHandle   : in     CommonTypes.Unsigned32T;
                                Template    : in out KeyTemplateT;
                                ReturnValue :    out ReturnValueT)
   is
   begin

       if (OwnerMask and
             Template.AttrMask) /= MaskT(0) then

          Template.Owner := KeyStore(KeyHandle).Owner;
       end if;

       if (KeyIDMask and
             Template.AttrMask) /= MaskT(0) then

          Template.KeyID := KeyStore(KeyHandle).KeyID;
       end if;

       if (KeyLengthMask and
             Template.AttrMask) /= MaskT(0) then

          Template.KeyLength := KeyStore(KeyHandle).KeyLength;
       end if;

       if (IsPublicMask and
             Template.AttrMask) /= MaskT(0) then

          Template.IsPublic := KeyStore(KeyHandle).IsPublic;
       end if;

       ReturnValue := Ok;

   exception
      when E : others =>
         ReturnValue := ObjectHandleInvalid;

   end GetAttributeValue;

   ------------------------------------------------------------------
   -- ClearStore
   --
   -- Description:
   --    Clears all data from the keystore file
   --
   ------------------------------------------------------------------
   procedure ClearStore is
      Status : SPARK_IO.File_Status;
      Keys   : SPARK_IO.File_Type;
   begin
      SPARK_IO.Open(File => Keys,
                    Mode_Of_File => SPARK_IO.Out_File,
                    Name_Of_File => "./System/keystore",
                    Form_Of_File => "",
                    Status       => Status);
      SPARK_IO.Close(File   => Keys,
                     Status => Status);
   end ClearStore;

end Crypto;
