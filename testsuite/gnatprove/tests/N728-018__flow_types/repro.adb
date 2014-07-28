procedure Repro with SPARK_Mode is

   package BasicTypes is
      type Unsigned32T is range 0 .. 2**32 - 1;
      for Unsigned32T'Size use 32;

      type Signed32T is range - (2**31) .. 2**31 - 1;
      for Signed32T'Size use 32;

      type ByteT is range 0..255;
      for ByteT'Size use 8;

      type PresenceT is (Present, Absent);
   end BasicTypes;

   package CryptoTypes is
      subtype NameCountT is Natural range 0..40;
      subtype NameI is NameCountT range 1..40;
      subtype NameT is String(NameI);
      BlankName : constant NameT := NameT'(others => ' ');

      type IssuerIDT is range 0..2**32 - 1;

      type IssuerT is
         record
            ID         : IssuerIDT;
            NameLength : NameCountT;
            Name       : NameT;
         end record;
   end CryptoTypes;

   package Crypto is
      subtype KeyPaddingIndexT is Integer range 1..67;
      type KeyPaddingT is array(KeyPaddingIndexT) of BasicTypes.ByteT;

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
         KeyID     : BasicTypes.Unsigned32T;  -- 4 bytes
         KeyLength : BasicTypes.Unsigned32T;  -- 4 bytes
         IsPublic  : Boolean;                 -- 1 byte
         Padding   : KeyPaddingT;             -- 128 - 61 = 67 bytes
      end record;

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
   end Crypto;

   subtype KeyPaddingIndexT is Integer range 1..67;
   type KeyPaddingT is array(KeyPaddingIndexT) of BasicTypes.ByteT;

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
      KeyID     : BasicTypes.Unsigned32T;  -- 4 bytes
      KeyLength : BasicTypes.Unsigned32T;  -- 4 bytes
      IsPublic  : Boolean;                 -- 1 byte
      Padding   : KeyPaddingT;             -- 128 - 61 = 67 bytes
   end record;

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

   function GetKeystoreReturn(CryptoRet : Crypto.ReturnValueT)
      return ReturnValueT
   is
   begin
      return ReturnValueT'Val(
                Crypto.ReturnValueT'Pos(
                   CryptoRet));
   end GetKeystoreReturn;

   procedure CreateObject(Template     : in     KeyTemplateT;
                          ReturnValue  :    out ReturnValueT)
   is
      LocalTemplate    : Crypto.KeyTemplateT :=
          (AttrMask  => Crypto.MaskT(Template.AttrMask),
           Owner     => Template.Owner,
           KeyID     => Template.KeyID,
           KeyLength => Template.KeyLength,
           IsPublic  => Template.IsPublic,
           Padding   => (others => 0));

      LocalReturnValue   : Crypto.ReturnValueT;
      UnusedObjectHandle : BasicTypes.Unsigned32T;
   begin
      ReturnValue := GetKeystoreReturn(LocalReturnValue);
   end CreateObject;
begin
   null;
end Repro;
