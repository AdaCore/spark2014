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
-- TokenAPI
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with TcpIp,
     CommonTypes,
     MsgProc,
     Ada.Strings.Fixed,
     Ada.Strings;

with Unchecked_Conversion;

use type CommonTypes.Unsigned32T;

package body TokenAPI
  with SPARK_Mode => Off
is
   PraxisCards : Boolean := False;

   ------------------------------------------------------------------
   -- Local subprograms
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ReaderTo32, CardTo32, CodeTo32
   --
   -- Description:
   --    Converts the enumerated type to a 32-bit unsigned value
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function ReaderTo32 is new
      Unchecked_Conversion (Source => ReaderStateT,
                            Target => CommonTypes.Unsigned32T);

   function CardTo32 is new
      Unchecked_Conversion (Source => CardStateT,
                            Target => CommonTypes.Unsigned32T);

   function CodeTo32 is new
      Unchecked_Conversion (Source => ResponseCodeT,
                            Target => CommonTypes.Unsigned32T);

   ------------------------------------------------------------------
   -- GetStringHandle
   --
   -- Description:
   --    turns the handle into a string, prepends with a
   --    'p' if it is a praxis card. PXS cards are always 2 digits.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function GetStringHandle(CardHandle   : in     CommonTypes.Unsigned32T)
     return String
   is
       StringHandle : String := Ada.Strings.Fixed.Trim(
                                   CommonTypes.Unsigned32T'Image(
                                      CardHandle), Ada.Strings.Both);

      PStringHandle : String(1..3) := "p00";
   begin
      if PraxisCards then
         PStringHandle(PStringHandle'Last - StringHandle'Length + 1
                       ..PStringHandle'Last) := StringHandle;
         return PStringHandle;
      else
         return StringHandle;
      end if;

   end GetStringHandle;

   ------------------------------------------------------------------
   -- Exported subprograms
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ListReaders
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ListReaders (List         :    out CommonTypes.String8ArrayT;
                          Number       : in out CommonTypes.Unsigned32T;
                          ResponseCode :    out CommonTypes.Unsigned32T)
   is
      InMsg     : TcpIp.MessageT;
      CommsIsOK : Boolean;
      OutMsg    : constant TcpIp.MessageT :=
                 (Data   => Ada.Strings.Fixed.Overwrite(
                                  Source   => TcpIp.NullMsg.Data,
                                  Position => 1,
                                  New_Item =>
                                       "tokenReader.listReaders('" &
                                       CommonTypes.Unsigned32T'Image(Number) &
                                       "',)"),
                  Length => 28 +
                            CommonTypes.Unsigned32T'Image(Number)'Length);


   begin
      List := (others => (others => ' '));

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is ('OK[:..]', 'No', ('Name1', 'Name2', ..))
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);

         begin

            Number := CommonTypes.Unsigned32T'Value(
                         MsgProc.GetStringByPos(Msg => Msg,
                                                Arg => 1));
            for i in CommonTypes.String8ArrayI'Range loop
               Ada.Strings.Fixed.Overwrite(List(i),
                                          1,
                                          MsgProc.GetStringByPos(Msg => Msg,
                                                                 Arg => i + 1));
               exit when i = CommonTypes.String8ArrayI(Number);
            end loop;

         end;
         ResponseCode := CodeTo32(Success);

      else
         -- Comms Fail - readers unavailable.
         Number := 0;
         ResponseCode := CodeTo32(ReaderUnavailable);
      end if;
   exception

      when E : others =>

         -- Exception - function cancelled
         Number := 0;
         ResponseCode := CodeTo32(Cancelled);

   end ListReaders;


   ------------------------------------------------------------------
   -- GetStatusChange
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetStatusChange (Timeout      : in     CommonTypes.Unsigned32T;
                              Reader       : in     CommonTypes.String8T;
                              CurrentState : in     ReaderStateT;
                              NewState     :    out CommonTypes.Unsigned32T;
                              ResponseCode :    out CommonTypes.Unsigned32T)
   is
      InMsg      : TcpIp.MessageT;
      CommsIsOK  : Boolean;
      TrimReader : String := Ada.Strings.Fixed.Trim(Reader, Ada.Strings.Both);

      OutMsg : constant TcpIp.MessageT :=
                 (Data   => Ada.Strings.Fixed.Overwrite(
                                  Source   => TcpIp.NullMsg.Data,
                                  Position => 1,
                                  New_Item => "tokenReader.getState('" &
                                              TrimReader & "',)"),
                  Length => 25 + TrimReader'Length);

      NewStateEnum : ReaderStateT;

   begin
      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is ('OK[:..]', {Dict})
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
                 StateDict : MsgProc.DictionaryT :=
                                MsgProc.GetDictionary(Msg => Msg,
                                                      Arg => 1);

         begin

            NewStateEnum := ReaderStateT'Value(MsgProc.GetStringByKey(
                                                   Dic => StateDict,
                                                   Key => "rState"));
            NewState := ReaderTo32(NewStateEnum);

            if NewStateEnum = CurrentState then
               ResponseCode := CodeTo32(TimedOut);
            else
               ResponseCode := CodeTo32(Success);
            end if;

         end;

      else
         -- Comms Fail - reader unavailable.
         NewState     := ReaderTo32(Unavailable);
         ResponseCode := CodeTo32(ReaderUnavailable);
      end if;

   exception

      when E : others =>

         -- Exception - function cancelled, NewState set to an invalid value
         NewState     := 0;
         ResponseCode := CodeTo32(Cancelled);

   end GetStatusChange;


   ------------------------------------------------------------------
   -- Connect
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Connect (Reader       : in     CommonTypes.String8T;
                      CardHandle   :    out CommonTypes.Unsigned32T;
                      ResponseCode :    out CommonTypes.Unsigned32T)
   is
      InMsg      : TcpIp.MessageT;
      CommsIsOK  : Boolean;
      TrimReader : String := Ada.Strings.Fixed.Trim(Reader, Ada.Strings.Both);

      OutMsg : constant TcpIp.MessageT :=
                 (Data   => Ada.Strings.Fixed.Overwrite(
                                  Source   => TcpIp.NullMsg.Data,
                                  Position => 1,
                                  New_Item => "tokenReader.connect('" &
                                              TrimReader & "',)"),
                  Length => 24 + TrimReader'Length);

   begin
      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is ('OK[:..]', 'Hndle')
         declare
            Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
            HandleStr : String := MsgProc.GetStringByPos(Msg => Msg,
                                                         Arg => 1);

         begin
            if HandleStr(HandleStr'First) = 'p' then
               PraxisCards := True;
               CardHandle := CommonTypes.Unsigned32T'Value(HandleStr(2..3));
            else
               PraxisCards := False;
               CardHandle := CommonTypes.Unsigned32T'Value(HandleStr);
            end if;

         end;

         ResponseCode := CodeTo32(Success);

      else
         -- Comms Fail - card unresponsive.
         CardHandle := 0;
         ResponseCode := CodeTo32(UnresponsiveCard);
      end if;
   exception

      when E : others =>

         -- Exception - function cancelled
         CardHandle := 0;
         ResponseCode := CodeTo32(Cancelled);

   end Connect;

   ------------------------------------------------------------------
   -- Status
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Status (CardHandle   : in     CommonTypes.Unsigned32T;
                     CState       :    out CommonTypes.Unsigned32T;
                     ATR          :    out AnswerToResetT;
                     ResponseCode :    out CommonTypes.Unsigned32T)
   is
      InMsg     : TcpIp.MessageT;
      CommsIsOK : Boolean;
      OutMsg : TcpIp.MessageT;

      NullATR : constant AnswerToResetT := (TokenID => 0,
                                            Padding => (others => 0));

      StringHandle : String := GetStringHandle(CardHandle);

   begin
      ATR := NullATR;

      OutMsg := (Data   => Ada.Strings.Fixed.Overwrite(
                                  Source   => TcpIp.NullMsg.Data,
                                  Position => 1,
                                  New_Item => "tokenReader.status('" &
                                              StringHandle & "',)"),
                  Length => 23 + StringHandle'Length);

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is ('OK[:..]', 'Cstate', 'TokenID')
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);

         begin

            CState := CardTo32(
                         CardStateT'Value(
                            MsgProc.GetStringByPos(Msg => Msg,
                                                   Arg => 1)));

            begin
               ATR.TokenID := CommonTypes.Unsigned32T'Value(
                                       MsgProc.GetStringByPos(Msg => Msg,
                                                              Arg => 2));
            exception
               when E : others =>
                  null;
            end;

         end;

         ResponseCode := CodeTo32(Success);

      else
         -- Comms Fail - card unresponsive.
         CState := CardTo32(Present);
         ResponseCode := CodeTo32(UnresponsiveCard);
      end if;
   exception

      when E : others =>

         -- Exception - function cancelled
         CState := CardTo32(Present);
         ResponseCode := CodeTo32(Cancelled);

   end Status;

   ------------------------------------------------------------------
   -- Disconnect
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Disconnect (CardHandle   : in     CommonTypes.Unsigned32T;
                         ResponseCode :    out CommonTypes.Unsigned32T)
   is
      InMsg        : TcpIp.MessageT;
      CommsIsOK    : Boolean;
      StringHandle : String := GetStringHandle(CardHandle);
      OutMsg       : TcpIp.MessageT;
   begin
      OutMsg := (Data   => Ada.Strings.Fixed.Overwrite(
                                  Source   => TcpIp.NullMsg.Data,
                                  Position => 1,
                                  New_Item => "tokenReader.disconnect('" &
                                              StringHandle & "',)"),
                 Length => 27 + StringHandle'Length);

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is ('OK[:..]', )
         ResponseCode := CodeTo32(Success);

      else
         -- Comms Fail - unresponsive card.
         ResponseCode := CodeTo32(UnresponsiveCard);
      end if;
   exception

      when E : others =>

         -- Exception - function cancelled
         ResponseCode := CodeTo32(Cancelled);

   end Disconnect;


   ------------------------------------------------------------------
   -- GetIDCert
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetIDCert (CardHandle   : in     CommonTypes.Unsigned32T;
                        RawIDCert    :    out GenericRawCertT;
                        StatusOK     :    out Boolean;
                        ResponseCode :    out CommonTypes.Unsigned32T)
   is
      InMsg        : TcpIp.MessageT;
      CommsIsOK    : Boolean;
      StringHandle : String := GetStringHandle(CardHandle);

      OutMsg : TcpIp.MessageT;

   begin
      OutMsg := (Data   => Ada.Strings.Fixed.Overwrite(
                                  Source   => TcpIp.NullMsg.Data,
                                  Position => 1,
                                  New_Item => "tokenReader.getIDCert('" &
                                              StringHandle & "',)"),
                 Length => 26 + StringHandle'Length);

      RawIDCert := NullGenericRawCert;

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is ('OK[:..]', 'StatusOK', {Dict})
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
                 RawCert : MsgProc.DictionaryT :=
                              MsgProc.GetDictionary(Msg => Msg,
                                                    Arg => 1);
         begin

            StatusOK := Boolean'Value(
                           MsgProc.GetStringByPos(Msg => Msg,
                                                  Arg => 1));
            if StatusOK then
               Ada.Strings.Fixed.Overwrite(
                             RawIDCert.CertData,
                             1,
                             String(RawCert));

               RawIDCert.CertLength := RawCert'Length;

               ResponseCode := CodeTo32(Success);
            else
               -- problems communicating with the card
               ResponseCode := CodeTo32(UnresponsiveCard);
            end if;
         end;

      else
         -- Comms Fail - reader unavailable.
         StatusOK     := False;
         ResponseCode := CodeTo32(ReaderUnavailable);
      end if;
   exception

      when E : others =>

         -- Exception - function cancelled
         StatusOK     := False;
         ResponseCode := CodeTo32(Cancelled);

   end GetIDCert;

   ------------------------------------------------------------------
   -- GetPrivCert
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetPrivCert (CardHandle   : in     CommonTypes.Unsigned32T;
                          RawPrivCert  :    out GenericRawCertT;
                          StatusOK     :    out Boolean;
                          ResponseCode :    out CommonTypes.Unsigned32T)
   is
      InMsg        : TcpIp.MessageT;
      CommsIsOK    : Boolean;
      StringHandle : String := GetStringHandle(CardHandle);
      OutMsg       : TcpIp.MessageT;
   begin
      OutMsg := (Data   => Ada.Strings.Fixed.Overwrite(
                                  Source   => TcpIp.NullMsg.Data,
                                  Position => 1,
                                  New_Item => "tokenReader.getPrivCert('" &
                                              StringHandle & "',)"),
                  Length => 28 + StringHandle'Length);

      RawPrivCert := NullGenericRawCert;

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is ('OK[:..]', 'StatusOK', {Dict})
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
                 RawCert : MsgProc.DictionaryT :=
                              MsgProc.GetDictionary(Msg => Msg,
                                                    Arg => 1);
         begin

            StatusOK := Boolean'Value(
                           MsgProc.GetStringByPos(Msg => Msg,
                                                  Arg => 1));
            if StatusOK then
               Ada.Strings.Fixed.Overwrite(
                             RawPrivCert.CertData,
                             1,
                             String(RawCert));

               RawPrivCert.CertLength := RawCert'Length;

               ResponseCode := CodeTo32(Success);
            else
               -- problems communicating with the card
               ResponseCode := CodeTo32(UnresponsiveCard);

            end if;
         end;
      else
         -- Comms Fail - reader unavailable.
         StatusOK     := False;
         ResponseCode := CodeTo32(ReaderUnavailable);
      end if;
   exception

      when E : others =>

         -- Exception - function cancelled
         StatusOK     := False;
         ResponseCode := CodeTo32(Cancelled);

   end GetPrivCert;

   ------------------------------------------------------------------
   -- GetIACert
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetIACert (CardHandle   : in     CommonTypes.Unsigned32T;
                        RawIACert    :    out GenericRawCertT;
                        StatusOK     :    out Boolean;
                        ResponseCode :    out CommonTypes.Unsigned32T)
   is
      InMsg        : TcpIp.MessageT;
      CommsIsOK    : Boolean;
      StringHandle : String := GetStringHandle(CardHandle);
      OutMsg       : TcpIp.MessageT;
   begin
      OutMsg := (Data   => Ada.Strings.Fixed.Overwrite(
                                  Source   => TcpIp.NullMsg.Data,
                                  Position => 1,
                                  New_Item => "tokenReader.getIACert('" &
                                              StringHandle & "',)"),
                 Length => 26 + StringHandle'Length);

      RawIACert := NullGenericRawCert;

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is ('OK[:..]', 'StatusOK', {Dict})
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
                 RawCert : MsgProc.DictionaryT :=
                              MsgProc.GetDictionary(Msg => Msg,
                                                    Arg => 1);
         begin

            StatusOK := Boolean'Value(
                           MsgProc.GetStringByPos(Msg => Msg,
                                                  Arg => 1));
            if StatusOK then
               Ada.Strings.Fixed.Overwrite(
                             RawIACert.CertData,
                             1,
                             String(RawCert));

               RawIACert.CertLength := RawCert'Length;

               ResponseCode := CodeTo32(Success);
            else
               -- problems communicating with the card
               ResponseCode := CodeTo32(UnresponsiveCard);

            end if;
         end;

      else
         -- Comms Fail - reader unavailable.
         StatusOK := False;
         ResponseCode := CodeTo32(ReaderUnavailable);
      end if;
   exception

      when E : others =>

         -- Exception - function cancelled
         StatusOK     := False;
         ResponseCode := CodeTo32(Cancelled);

   end GetIACert;

   ------------------------------------------------------------------
   -- GetAuthCert
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetAuthCert (CardHandle   : in     CommonTypes.Unsigned32T;
                          RawAuthCert  :    out GenericRawCertT;
                          Exists       :    out Boolean;
                          StatusOK     :    out Boolean;
                          ResponseCode :    out CommonTypes.Unsigned32T)
   is
      InMsg        : TcpIp.MessageT;
      CommsIsOK    : Boolean;
      StringHandle : String := GetStringHandle(CardHandle);
      OutMsg       : TcpIp.MessageT;
   begin
      OutMsg := (Data   => Ada.Strings.Fixed.Overwrite(
                                  Source   => TcpIp.NullMsg.Data,
                                  Position => 1,
                                  New_Item => "tokenReader.getAuthCert('" &
                                              StringHandle & "',)"),
                  Length => 28 + StringHandle'Length);
      RawAuthCert := NullGenericRawCert;

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is ('OK[:..]', 'StatusOK', {Dict})
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
                 RawCert : MsgProc.DictionaryT :=
                              MsgProc.GetDictionary(Msg => Msg,
                                                    Arg => 1);
         begin

            StatusOK := Boolean'Value(
                           MsgProc.GetStringByPos(Msg => Msg,
                                                  Arg => 1));
            Exists := Boolean'Value(
                           MsgProc.GetStringByPos(Msg => Msg,
                                                  Arg => 2));

            if StatusOK and Exists then
               Ada.Strings.Fixed.Overwrite(
                             RawAuthCert.CertData,
                             1,
                             String(RawCert));

               RawAuthCert.CertLength := RawCert'Length;

               ResponseCode := CodeTo32(Success);
            else
               -- problems communicating with the card
               ResponseCode := CodeTo32(UnresponsiveCard);
            end if;
         end;

      else
         -- Comms Fail - reader unavailable.
         StatusOK := False;
         Exists   := False;
         ResponseCode := CodeTo32(ReaderUnavailable);
      end if;
   exception

      when E : others =>

         -- Exception - function cancelled
         StatusOK     := False;
         Exists       := False;
         ResponseCode := CodeTo32(Cancelled);

   end GetAuthCert;

   ------------------------------------------------------------------
   -- UpdateAuthCert
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure UpdateAuthCert (CardHandle   : in     CommonTypes.Unsigned32T;
                             RawAuthCert  : in     GenericRawCertT;
                             StatusOK     :    out Boolean;
                             ResponseCode :    out CommonTypes.Unsigned32T)
   is
      InMsg,
      OutMsg    : TcpIp.MessageT;
      ValuesOK,
      CommsIsOK : Boolean;

      procedure ConstructUpdateMessage(Success : out Boolean)
      is
         StringHandle : String := GetStringHandle(CardHandle);
         StringData   : String := RawAuthCert.CertData(
                                     1..Integer(RawAuthCert.CertLength));

         NewItem      : String := "tokenReader.updateAuthCert('" &
                                   StringHandle &
                                   "', {" &
                                   StringData &
                                   "})";

      begin

         OutMsg.Data := Ada.Strings.Fixed.Overwrite(
                           Source   => TcpIp.NullMsg.Data,
                           Position => 1,
                           New_Item => NewItem);

         OutMsg.Length := NewItem'Length;
         Success := True;

      exception

         when E : others =>

            OutMsg  := TcpIp.NullMsg;
            Success := False;
      end ConstructUpdateMessage;

   begin

      ConstructUpdateMessage(Success => ValuesOK);

      if ValuesOk then
         TcpIp.SendAndReceive (IsAdmin  => False,
                               Outgoing => OutMsg,
                               Incoming => InMsg,
                               Success  => CommsIsOK);

         if CommsIsOK then
            -- InMsg.Data is ('OK[:..], 'StatusOK')
            declare Msg : String :=
                       MsgProc.GetResponseFromMsg(InMsg);
            begin
               StatusOK := Boolean'Value(
                              MsgProc.GetStringByPos(Msg => Msg,
                                                     Arg => 1));

               if StatusOK then
                  ResponseCode := CodeTo32(Success);
               else
                  -- problems communicating with the card
                  ResponseCode := CodeTo32(UnresponsiveCard);
               end if;
            end;

         else
            -- Comms Fail - reader unavailable.
            StatusOK := False;
            ResponseCode := CodeTo32(ReaderUnavailable);
         end if;

      else
         -- Problem Creating the Message
         StatusOK := False;
         ResponseCode := CodeTo32(InvalidValue);
      end if;

   exception

      when E : others =>

         -- Exception - function cancelled
         StatusOK     := False;
         ResponseCode := CodeTo32(Cancelled);

   end UpdateAuthCert;

end TokenAPI;
