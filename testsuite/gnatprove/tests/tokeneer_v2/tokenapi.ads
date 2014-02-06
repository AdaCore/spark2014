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
-- Description:
--    Token Reader Interfac.
--    This API mirrors definitions from the PC/SC ICC Resource Manager
--    Definition. Procedures model those given in the Microsoft Security SDK,
--    with one notable exception - the ScardTransmit function. This generic
--    function will be modeled in this system by specific procedures GetIDCert,
--    GetPrivCert, GetIACert, GetAuthCert and UpdateAuthCert.
--
------------------------------------------------------------------

with CommonTypes;

package TokenAPI is

   ------------------------------------------------------------------
   -- Types
   --
   --
   -- All outputs from the test drivers to TIS are raw (Unsigned32) to allow
   -- erroneous data to be passed back into TIS,
   -- which TIS must then deal with.
   --
   ------------------------------------------------------------------

   -- ResponseCodeT provides a means of examining the success or otherwise of
   -- an executed command.

   type ResponseCodeT is
      (Success,             -- No error.
       InvalidHandle,       -- Supplied handle is invalid.
       InvalidValue,        -- Parameter Value(s) could not be
                            -- properly interpreted.
       Cancelled,           -- Action was cancelled by the
                            -- application.
       NoMemory,            -- Not enough memory to complete
                            -- command.
       InsufficientBuffer,  -- Data buffer to receive returned
                            -- data is too small.
       UnknownReader,       -- Reader name is not recognized.
       Timedout,             -- Timeout has expired.
       SharingViolation,    -- ICC cannot be accessed -
                            -- outstanding connections.
       NoSmartcard,         -- Required ICC not in device.
       UnknownCard,         -- Specified name is not recognized.
       ProtoMismatch,       -- Requested protocols incompatible
                            -- with protocol currently in use
                            -- with the ICC.
       NotReady,            -- Device or card not ready for
                            -- commands.
       SystemCancelled,     -- Action cancelled by system.
       ReaderUnavailable,   -- Device not currently available
                            -- for use.
       UnsupportedCard,     -- Reader cannot communicate, due to
                            -- ATR conflicts.
       UnresponsiveCard,    -- Card not responding to a reset.
       UnpoweredCard,       -- Power has been removed from the
                            -- card.
       ResetCard,           -- Card has been reset, so any
                            -- shared state info is invalid.
       RemovedCard);        -- ICC has been removed.

   for ResponseCodeT use
      (Success             => 0,
       InvalidHandle       => 1,
       InvalidValue        => 2,
       Cancelled           => 3,
       NoMemory            => 4,
       InsufficientBuffer  => 5,
       UnknownReader       => 6,
       Timedout            => 7,
       SharingViolation    => 8,
       NoSmartcard         => 9,
       UnknownCard         => 10,
       ProtoMismatch       => 11,
       NotReady            => 12,
       SystemCancelled     => 13,
       ReaderUnavailable   => 14,
       UnsupportedCard     => 15,
       UnresponsiveCard    => 16,
       UnpoweredCard       => 17,
       ResetCard           => 18,
       RemovedCard         => 19);

   for ResponseCodeT'Size use 32;

   -- CardStateT reflects the possible states of a card in a reader:

   type CardStateT is
      (Absent,      -- No card in the reader.
       Present,     -- Card in the reader, but not in position
                    -- for use.
       Swallowed,   -- Card in reader, in position for use. Card
                    -- is not powered.
       Powered,     -- Power is being provided to the card, but
                    -- reader driver is unaware of the mode of
                    -- the card.
       Negotiable,  -- Card has been reset and is awaiting PTS
                    -- negotiation.
       Specific);   -- Card has been reset and specific
                    -- protocols have been established.

   for CardStateT use
      (Absent     => 1,
       Present    => 2,
       Swallowed  => 3,
       Powered    => 4,
       Negotiable => 5,
       Specific   => 6);

   for CardStateT'Size use 32;

   -- ReaderStateT represents the possible states of a reader.

   type ReaderStateT is
      (Unaware,     -- State is unknown by the application
       Ignore,      -- Reader should be ignored
       Unavailable, -- Reader is not available for use
       Empty,       -- No card in the reader
       Present,     -- A card is present in the reader
       Mute);       -- An unresponsive card is in the reader

   for ReaderStateT use (Unaware     => 1,
                         Ignore      => 2,
                         Unavailable => 3,
                         Empty       => 4,
                         Present     => 5,
                         Mute        => 6);

   for ReaderStateT'Size use 32;

   -- AnswerToResetT represents the card's answer-to-reset that is sent from
   -- the card to the reader after a successful reset. The only part of this
   -- that we are interested in is the token's ID, which is used in the
   -- validation of certificates held on the card (The ID certificate's serial
   -- number is equal to this).

   type ATRPadding is Array(1..7) of CommonTypes.Unsigned32T;

   type AnswerToResetT is record
      TokenID : CommonTypes.Unsigned32T;
      Padding : ATRPadding;
   end record;


   -- Certificate types sent and returned to the card are considered to
   -- be raw, i.e. a string. The structure and size of the data
   -- contained within the certificates is as defined in the
   -- Certificate Processing library. GenericRawCertT is used to
   -- represent any kind of certificate, and contains two fields.
   -- CertData is the certificate itself which will be entered at
   -- position 1 and take up as much of the array as necessary; CertLength
   -- is the actual amount of data (in characters) stored in the
   -- CertData String.

   subtype GenericCertArray is String(1..4096);

   type GenericRawCertT is record
      CertData   : GenericCertArray;
      CertLength : CommonTypes.Unsigned32T;
   end record;

   NullGenericRawCert : constant GenericRawCertT := ((others => ' '),
                                                     0);

   ------------------------------------------------------------------
   -- ListReaders
   --
   -- Description:
   --    ListReaders will be called at initialisation to provide the TIS with
   --    a list of strings used to interface with visible token readers.
   --
   ------------------------------------------------------------------
   procedure ListReaders (List         :    out CommonTypes.String8ArrayT;
                          Number       : in out CommonTypes.Unsigned32T;
                          ResponseCode :    out CommonTypes.Unsigned32T);


   ------------------------------------------------------------------
   -- GetStatusChange
   --
   -- Description:
   --    Used by TIS as a means of 'polling' the reader, to determine whether
   --    a card is present.
   --
   ------------------------------------------------------------------
   procedure GetStatusChange (Timeout      : in     CommonTypes.Unsigned32T;
                              Reader       : in     CommonTypes.String8T;
                              CurrentState : in     ReaderStateT;
                              NewState     :    out CommonTypes.Unsigned32T;
                              ResponseCode :    out CommonTypes.Unsigned32T);

   ------------------------------------------------------------------
   -- Connect
   --
   -- Description:
   --    Connect is called once GetStatusChange has determined that a card is
   --    present in a reader, and establishes a connection between TIS and the
   --    card in the reader.
   --
   ------------------------------------------------------------------
   procedure Connect (Reader       : in     CommonTypes.String8T;
                      CardHandle   :    out CommonTypes.Unsigned32T;
                      ResponseCode :    out CommonTypes.Unsigned32T);

   ------------------------------------------------------------------
   -- Status
   --
   -- Description:
   --    Status will be called once a card has been connected to provide TIS
   --    with the status of the card. This can be used to obtain the card's
   --    unique ID, contained in the answer-to-reset (ATR). The ATR is
   --    only defined if the card is in 'Negotiable' or 'Specific' state, so
   --    should be ignored when the card is in any other state.
   --
   ------------------------------------------------------------------
   procedure Status (CardHandle   : in     CommonTypes.Unsigned32T;
                     CState       :    out CommonTypes.Unsigned32T;
                     ATR          :    out AnswerToResetT;
                     ResponseCode :    out CommonTypes.Unsigned32T);

   ------------------------------------------------------------------
   -- Disconnect
   --
   -- Description:
   --    Disconnect is called once TIS has finished communications with the
   --    card.
   --
   ------------------------------------------------------------------
   procedure Disconnect (CardHandle   : in     CommonTypes.Unsigned32T;
                         ResponseCode :    out CommonTypes.Unsigned32T);


   ------------------------------------------------------------------
   -- GetIDCert
   --
   -- Description:
   --    GetIDCert is called by TIS once it is in communication with a card,
   --    and is used to obtain the ID certificate from that card.
   --    StatusOK reports whether card communications were OK or not.
   --
   ------------------------------------------------------------------
   procedure GetIDCert (CardHandle   : in     CommonTypes.Unsigned32T;
                        RawIDCert    :    out GenericRawCertT;
                        StatusOK     :    out Boolean;
                        ResponseCode :    out CommonTypes.Unsigned32T);

   ------------------------------------------------------------------
   -- GetPrivCert
   --
   -- Description:
   --    GetPrivCert is called by TIS once it is in communication with a card,
   --    and is used to obtain the Privilege certificate from that card.
   --    StatusOK reports whether card communications were OK or not.
   --
   ------------------------------------------------------------------
   procedure GetPrivCert (CardHandle   : in     CommonTypes.Unsigned32T;
                          RawPrivCert  :    out GenericRawCertT;
                          StatusOK     :    out Boolean;
                          ResponseCode :    out CommonTypes.Unsigned32T);

   ------------------------------------------------------------------
   -- GetIACert
   --
   -- Description:
   --    GetIACert is called by TIS once it is in communication with a card,
   --    and is used to obtain the I&A certificate from that card.
   --    StatusOK reports whether card communications were OK or not.
   --
   ------------------------------------------------------------------
   procedure GetIACert (CardHandle   : in     CommonTypes.Unsigned32T;
                        RawIACert    :    out GenericRawCertT;
                        StatusOK     :    out Boolean;
                        ResponseCode :    out CommonTypes.Unsigned32T);

   ------------------------------------------------------------------
   -- GetAuthCert
   --
   -- Description:
   --    GetAuthCert is called by TIS once it is in communication with a card,
   --    and is used to obtain the Authorisation certificate from that card.
   --    There may not be an Auth Cert; Exists indicates this.
   --    StatusOK reports whether card communications were OK or not.
   --
   ------------------------------------------------------------------
   procedure GetAuthCert (CardHandle   : in     CommonTypes.Unsigned32T;
                          RawAuthCert  :    out GenericRawCertT;
                          Exists       :    out Boolean;
                          StatusOK     :    out Boolean;
                          ResponseCode :    out CommonTypes.Unsigned32T);

   ------------------------------------------------------------------
   -- UpdateAuthCert
   --
   -- Description:
   --    UpdateAuthCert is called when a new Auth Cert has been created for a
   --    user, and attempts to write the provided Auth Cert to the user's card.
   --    StatusOK reports whether card communications were OK or not.
   --
   ------------------------------------------------------------------
   procedure UpdateAuthCert (CardHandle   : in     CommonTypes.Unsigned32T;
                             RawAuthCert  : in     GenericRawCertT;
                             StatusOK     :    out Boolean;
                             ResponseCode :    out CommonTypes.Unsigned32T);

end TokenAPI;
