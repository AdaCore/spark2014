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
-- TokenReader.Interface
--
-- Description:
--    Interfaces to the TokenAPI.
--
------------------------------------------------------------------
with BasicTypes;
with CertTypes;
with TokenTypes;
--# inherit
--#    BasicTypes,
--#    CertTypes,
--#    TokenTypes;

private package TokenReader.Interface
--# own in     ReaderInput,
--#     in     ReaderStatus,
--#        out ReaderOutput;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type CardHandleT is private;
   NullHandle : constant CardHandleT;

   subtype ReaderNameI is Positive range 1..8;
   subtype ReaderNameT is String(ReaderNameI);

   subtype ReaderArrayI is Positive range 1..10;
   type ReaderNameArrayT is Array(ReaderArrayI) of ReaderNameT;


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
       RemovedCard,         -- ICC has been removed.
       InvalidResponseCode);



   type CardStateT is
      (InvalidCardState,
       Absent,      -- No card in the reader.
       Present,     -- Card in the reader, but not in position
                    -- for use.
       Swallowed,   -- Card in reader, in position for use. Card
                    -- is not powered.
       Powered,     -- Power is being provided to the card, but
                    -- reader driver is unaware of the mode of
                    -- the card.
       Negotiable,  -- Card has been reset and is awaiting PTS
                    -- negotiation.
       Specific     -- Card has been reset and specific
                    -- protocols have been established.
       );


   type ReaderStateT is
      (InvalidReaderState,
       Unaware,     -- State is unknown by the application
       Ignore,      -- Reader should be ignored
       Unavailable, -- Reader is not available for use
       Empty,       -- No card in the reader
       CardPresent, -- A card is present in the reader
       Mute         -- An unresponsive card is in the reader
       );

   subtype ValidReaderStateT is ReaderStateT range Unaware .. Mute;

   ------------------------------------------------------------------
   -- ListReaders
   --
   -- Description:
   --    ListReaders will be called at initialisation to provide the TIS with
   --    a list of strings used to interface with visible token readers.
   --
   ------------------------------------------------------------------

   procedure ListReaders (List         :    out ReaderNameArrayT;
                          Number       : in out BasicTypes.Unsigned32T;
                          ResponseCode :    out BasicTypes.Unsigned32T);
   --# global in ReaderStatus;
   --# derives Number,
   --#         List,
   --#         ResponseCode from Number,
   --#                           ReaderStatus;


   ------------------------------------------------------------------
   -- GetStatusChange
   --
   -- Description:
   --    Used by TIS as a means of 'polling' the reader, to determine whether
   --    a card is present.
   --
   ------------------------------------------------------------------

   procedure GetStatusChange (Timeout      : in     BasicTypes.Unsigned32T;
                              Reader       : in     ReaderNameT;
                              CurrentState : in     ReaderStateT;
                              NewState     :    out BasicTypes.Unsigned32T;
                              ResponseCode :    out BasicTypes.Unsigned32T);
   --# global in ReaderStatus;
   --# derives ResponseCode from ReaderStatus,
   --#                           Timeout,
   --#                           Reader,
   --#                           CurrentState &
   --#         NewState     from ReaderStatus,
   --#                           Timeout,
   --#                           Reader;


   ------------------------------------------------------------------
   -- Connect
   --
   -- Description:
   --    Connect is called once GetStatusChange has determined that a card is
   --    present in a reader, and establishes a connection between TIS and the
   --    card in the reader.
   --
   ------------------------------------------------------------------

   procedure Connect (Reader       : in     ReaderNameT;
                      CardHandle   :    out CardHandleT;
                      ResponseCode :    out BasicTypes.Unsigned32T);

   --# global in ReaderStatus;
   --# derives ResponseCode,
   --#         CardHandle   from ReaderStatus,
   --#                           Reader;

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

   procedure Status (CardHandle   : in     CardHandleT;
                     CState       :    out BasicTypes.Unsigned32T;
                     ATR          :    out TokenTypes.TokenIDT;
                     ResponseCode :    out BasicTypes.Unsigned32T);

   --# global in ReaderStatus;
   --#        in ReaderInput;
   --# derives ResponseCode,
   --#         CState       from ReaderStatus,
   --#                           CardHandle &
   --#         ATR          from ReaderStatus,
   --#                           CardHandle,
   --#                           ReaderInput;

   ------------------------------------------------------------------
   -- Disconnect
   --
   -- Description:
   --    Disconnect is called once TIS has finished communications with the
   --    card.
   --
   ------------------------------------------------------------------

   procedure Disconnect (CardHandle   : in     CardHandleT;
                         ResponseCode :    out BasicTypes.Unsigned32T);

   --# global in ReaderStatus;
   --# derives ResponseCode from ReaderStatus,
   --#                           CardHandle;


   ------------------------------------------------------------------
   -- GetIDCert
   --
   -- Description:
   --    GetIDCert is called by TIS once it is in communication with a card,
   --    and is used to obtain the ID certificate from that card.
   --    StatusOK reports whether card communications were OK or not.
   --
   ------------------------------------------------------------------

   procedure GetIDCert (CardHandle   : in     CardHandleT;
                        RawIDCert    :    out CertTypes.RawCertificateT;
                        StatusOK     :    out Boolean;
                        ResponseCode :    out BasicTypes.Unsigned32T);

   --# global in ReaderStatus;
   --#        in ReaderInput;
   --# derives ResponseCode,
   --#         StatusOK     from ReaderStatus,
   --#                           CardHandle &
   --#         RawIDCert    from ReaderStatus,
   --#                           CardHandle,
   --#                           ReaderInput;

   ------------------------------------------------------------------
   -- GetPrivCert
   --
   -- Description:
   --    GetPrivCert is called by TIS once it is in communication with a card,
   --    and is used to obtain the Privilege certificate from that card.
   --    StatusOK reports whether card communications were OK or not.
   --
   ------------------------------------------------------------------

   procedure GetPrivCert (CardHandle   : in     CardHandleT;
                          RawPrivCert  :    out CertTypes.RawCertificateT;
                          StatusOK     :    out Boolean;
                          ResponseCode :    out BasicTypes.Unsigned32T);

   --# global in ReaderStatus;
   --#        in ReaderInput;
   --# derives ResponseCode,
   --#         StatusOK     from ReaderStatus,
   --#                           CardHandle &
   --#         RawPrivCert  from ReaderStatus,
   --#                           CardHandle,
   --#                           ReaderInput;

   ------------------------------------------------------------------
   -- GetIACert
   --
   -- Description:
   --    GetIACert is called by TIS once it is in communication with a card,
   --    and is used to obtain the I&A certificate from that card.
   --    StatusOK reports whether card communications were OK or not.
   --
   ------------------------------------------------------------------

   procedure GetIACert (CardHandle   : in     CardHandleT;
                        RawIACert    :    out CertTypes.RawCertificateT;
                        StatusOK     :    out Boolean;
                        ResponseCode :    out BasicTypes.Unsigned32T);

   --# global in ReaderStatus;
   --#        in ReaderInput;
   --# derives ResponseCode,
   --#         StatusOK     from ReaderStatus,
   --#                           CardHandle &
   --#         RawIACert    from ReaderStatus,
   --#                           CardHandle,
   --#                           ReaderInput;

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

   procedure GetAuthCert (CardHandle   : in     CardHandleT;
                          RawAuthCert  :    out CertTypes.RawCertificateT;
                          Exists       :    out Boolean;
                          StatusOK     :    out Boolean;
                          ResponseCode :    out BasicTypes.Unsigned32T);

   --# global in ReaderStatus;
   --#        in ReaderInput;
   --# derives ResponseCode,
   --#         StatusOK,
   --#         Exists       from ReaderStatus,
   --#                           CardHandle &
   --#         RawAuthCert  from ReaderStatus,
   --#                           CardHandle,
   --#                           ReaderInput;

   ------------------------------------------------------------------
   -- UpdateAuthCert
   --
   -- Description:
   --    UpdateAuthCert is called when a new Auth Cert has been created for a
   --    user, and attempts to write the provided Auth Cert to the user's card.
   --    StatusOK reports whether card communications were OK or not.
   --
   ------------------------------------------------------------------

   procedure UpdateAuthCert (CardHandle   : in     CardHandleT;
                             RawAuthCert  : in     CertTypes.RawCertificateT;
                             StatusOK     :    out Boolean;
                             ResponseCode :    out BasicTypes.Unsigned32T);
   --# global in     ReaderStatus;
   --#           out ReaderOutput;
   --# derives ResponseCode,
   --#         StatusOK     from ReaderStatus,
   --#                           CardHandle &
   --#         ReaderOutput from ReaderStatus,
   --#                           CardHandle,
   --#                           RawAuthCert;

private

   type CardHandleT is range 0 .. 2**32 - 1;
   for CardHandleT'Size use 32;
   NullHandle : constant CardHandleT := 0;

end TokenReader.Interface;
