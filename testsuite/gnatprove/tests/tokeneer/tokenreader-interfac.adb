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
-- TokenReader.Interfac
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with CommonTypes;
with TokenAPI;
with Ada.Strings.Fixed,
     Ada.Strings;

package body TokenReader.Interfac
  with SPARK_Mode => Off
is

   ------------------------------------------------------------------
   -- ConvertToTISRawCert
   --
   -- Description:
   --   Converts a GenericRawCert to a CertTypes.RawCertificate.
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   function ConvertToTISRawCert (Cert : TokenAPI.GenericRawCertT)
                                return CertTypes.RawCertificateT is
     (Cert.CertData);

   ------------------------------------------------------------------
   -- ConvertFromTISRawCert
   --
   -- Description:
   --   Converts a  CertTypes.RawCertificate to a GenericRawCert.
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   function ConvertFromTISRawCert (Cert : CertTypes.RawCertificateT)
                                  return TokenAPI.GenericRawCertT
   is
      TrimmedCert : constant String :=
        Ada.Strings.Fixed.Trim (Source => Cert,
                                Side   => Ada.Strings.Right);
   begin
       return
         (CertData   => Ada.Strings.Fixed.Overwrite
            (Source   => TokenApi.NullGenericRawCert.CertData,
             Position => 1,
             New_Item => TrimmedCert),
          CertLength => TrimmedCert'Length);
   end ConvertFromTISRawCert;

   ------------------------------------------------------------------
   -- ListReaders
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure ListReaders (List         :    out ReaderNameArrayT;
                          Number       : in out CommonTypes.Unsigned32T;
                          ResponseCode :    out CommonTypes.Unsigned32T)
   is
      LocalResponseCode : CommonTypes.Unsigned32T;
      LocalNumber       : CommonTypes.Unsigned32T :=
        CommonTypes.Unsigned32T (Number);
      LocalList         : CommonTypes.String8ArrayT;
   begin
      TokenAPI.ListReaders (List         => LocalList,
                            Number       => LocalNumber,
                            ResponseCode => LocalResponseCode);

      for J in ReaderArrayI loop
         List (J) := LocalList(J);
      end loop;

      Number       := CommonTypes.Unsigned32T (LocalNumber);
      ResponseCode := CommonTypes.Unsigned32T (LocalResponseCode);
   end ListReaders;

   ------------------------------------------------------------------
   -- GetStatusChange
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure GetStatusChange (Timeout      : in     CommonTypes.Unsigned32T;
                              Reader       : in     ReaderNameT;
                              CurrentState : in     ReaderStateT;
                              NewState     :    out CommonTypes.Unsigned32T;
                              ResponseCode :    out CommonTypes.Unsigned32T)
   is
      LocalResponseCode : CommonTypes.Unsigned32T;
      LocalCurrentState : TokenAPI.ReaderStateT;
      LocalNewState     : CommonTypes.Unsigned32T;
   begin
      LocalCurrentState := TokenAPI.ReaderStateT'Val
          (TokenAPI.ReaderStateT'Pos(TokenAPI.Unaware) +
           ReaderStateT'Pos(CurrentState) - ReaderStateT'Pos(Unaware));
      TokenAPI.GetStatusChange
        (Timeout       =>  CommonTypes.Unsigned32T(Timeout),
          Reader       =>  Reader,
          CurrentState => LocalCurrentState,
          NewState     => LocalNewState,
          ResponseCode => LocalResponseCode);

      NewState     := CommonTypes.Unsigned32T(LocalNewState);
      ResponseCode := CommonTypes.Unsigned32T(LocalResponseCode);
   end GetStatusChange;

   ------------------------------------------------------------------
   -- Connect
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure Connect (Reader       : in     ReaderNameT;
                      CardHandle   :    out CardHandleT;
                      ResponseCode :    out CommonTypes.Unsigned32T)
   is
      LocalResponseCode : CommonTypes.Unsigned32T;
      LocalCardHandle   : CommonTypes.Unsigned32T;
   begin
      TokenAPI.Connect
        (Reader       => Reader,
         CardHandle   => LocalCardHandle,
         ResponseCode => LocalResponseCode);

      CardHandle   := CardHandleT(LocalCardHandle);
      ResponseCode := CommonTypes.Unsigned32T(LocalResponseCode);
   end Connect;

   ------------------------------------------------------------------
   -- Status
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure Status (CardHandle   : in     CardHandleT;
                     CState       :    out CommonTypes.Unsigned32T;
                     ATR          :    out TokenTypes.TokenIDT;
                     ResponseCode :    out CommonTypes.Unsigned32T)
   is
      LocalResponseCode : CommonTypes.Unsigned32T;
      LocalCState       :  CommonTypes.Unsigned32T;
      LocalATR          : TokenAPI.AnswerToResetT;
   begin
      TokenAPI.Status
        (CardHandle   => CommonTypes.Unsigned32T(CardHandle),
         CState       => LocalCState,
         ATR          => LocalATR,
         ResponseCode => LocalResponseCode);

      ATR          := TokenTypes.TokenIDT(LocalATR.TokenID);
      CState       := CommonTypes.Unsigned32T(LocalCState);
      ResponseCode := CommonTypes.Unsigned32T(LocalResponseCode);
   end Status;

   ------------------------------------------------------------------
   -- Disconnect
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure Disconnect (CardHandle   : in     CardHandleT;
                         ResponseCode :    out CommonTypes.Unsigned32T)
   is
      LocalResponseCode : CommonTypes.Unsigned32T;
   begin
      TokenAPI.Disconnect
        (CardHandle   => CommonTypes.Unsigned32T(CardHandle),
         ResponseCode => LocalResponseCode);

      ResponseCode := CommonTypes.Unsigned32T(LocalResponseCode);
   end Disconnect;

   ------------------------------------------------------------------
   -- GetIDCert
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure GetIDCert (CardHandle   : in     CardHandleT;
                        RawIDCert    :    out CertTypes.RawCertificateT;
                        StatusOK     :    out Boolean;
                        ResponseCode :    out CommonTypes.Unsigned32T)
   is
      LocalResponseCode : CommonTypes.Unsigned32T;
      LocalRawCert      : TokenAPI.GenericRawCertT;
   begin
      TokenAPI.GetIDCert
        (CardHandle   => CommonTypes.Unsigned32T(CardHandle),
         RawIDCert    => LocalRawCert,
         StatusOK     => StatusOK,
         ResponseCode => LocalResponseCode);

      RawIDCert    := ConvertToTISRawCert(LocalRawCert);
      ResponseCode := CommonTypes.Unsigned32T(LocalResponseCode);
   end GetIDCert;

   ------------------------------------------------------------------
   -- GetPrivCert
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure GetPrivCert (CardHandle   : in     CardHandleT;
                          RawPrivCert  :    out CertTypes.RawCertificateT;
                          StatusOK     :    out Boolean;
                          ResponseCode :    out CommonTypes.Unsigned32T)
   is
      LocalResponseCode : CommonTypes.Unsigned32T;
      LocalRawCert      : TokenAPI.GenericRawCertT;
   begin
      TokenAPI.GetPrivCert
        (CardHandle   => CommonTypes.Unsigned32T(CardHandle),
         RawPrivCert  => LocalRawCert,
         StatusOK     => StatusOK,
         ResponseCode => LocalResponseCode);

      RawPrivCert  := ConvertToTISRawCert(LocalRawCert);
      ResponseCode := CommonTypes.Unsigned32T(LocalResponseCode);
   end GetPrivCert;

   ------------------------------------------------------------------
   -- GetIACert
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure GetIACert (CardHandle   : in     CardHandleT;
                        RawIACert    :    out CertTypes.RawCertificateT;
                        StatusOK     :    out Boolean;
                        ResponseCode :    out CommonTypes.Unsigned32T)
   is
      LocalResponseCode : CommonTypes.Unsigned32T;
      LocalRawCert      : TokenAPI.GenericRawCertT;
   begin
      TokenAPI.GetIACert
        (CardHandle   => CommonTypes.Unsigned32T(CardHandle),
         RawIACert    => LocalRawCert,
         StatusOK     => StatusOK,
         ResponseCode => LocalResponseCode);

      RawIACert    := ConvertToTISRawCert(LocalRawCert);
      ResponseCode := CommonTypes.Unsigned32T(LocalResponseCode);
   end GetIACert;

   ------------------------------------------------------------------
   -- GetAuthCert
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure GetAuthCert (CardHandle   : in     CardHandleT;
                          RawAuthCert  :    out CertTypes.RawCertificateT;
                          Exists       :    out Boolean;
                          StatusOK     :    out Boolean;
                          ResponseCode :    out CommonTypes.Unsigned32T)
   is
      LocalResponseCode : CommonTypes.Unsigned32T;
      LocalRawCert      : TokenAPI.GenericRawCertT;
   begin
      TokenAPI.GetAuthCert
        (CardHandle   => CommonTypes.Unsigned32T(CardHandle),
         RawAuthCert  => LocalRawCert,
         Exists       => Exists,
         StatusOK     => StatusOK,
         ResponseCode => LocalResponseCode);

      RawAuthCert  := ConvertToTISRawCert(LocalRawCert);
      ResponseCode := CommonTypes.Unsigned32T(LocalResponseCode);
   end GetAuthCert;

   ------------------------------------------------------------------
   -- UpdateAuthCert
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure UpdateAuthCert (CardHandle   : in     CardHandleT;
                             RawAuthCert  : in     CertTypes.RawCertificateT;
                             StatusOK     :    out Boolean;
                             ResponseCode :    out CommonTypes.Unsigned32T)
   is
      LocalResponseCode : CommonTypes.Unsigned32T;
   begin
      TokenAPI.UpdateAuthCert
        (CardHandle   => CommonTypes.Unsigned32T(CardHandle),
         RawAuthCert  => ConvertFromTISRawCert(RawAuthCert),
         StatusOK     => StatusOK,
         ResponseCode => LocalResponseCode);

      ResponseCode := CommonTypes.Unsigned32T(LocalResponseCode);
   end UpdateAuthCert;

end TokenReader.Interfac;
