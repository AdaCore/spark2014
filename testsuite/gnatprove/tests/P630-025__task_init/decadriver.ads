-------------------------------------------------------------------------------
--  Copyright (c) 2016 Daniel King
--
--  Permission is hereby granted, free of charge, to any person obtaining a
--  copy of this software and associated documentation files (the "Software"),
--  to deal in the Software without restriction, including without limitation
--  the rights to use, copy, modify, merge, publish, distribute, sublicense,
--  and/or sell copies of the Software, and to permit persons to whom the
--  Software is furnished to do so, subject to the following conditions:
--
--  The above copyright notice and this permission notice shall be included in
--  all copies or substantial portions of the Software.
--
--  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
--  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
--  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
--  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
--  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
--  DEALINGS IN THE SOFTWARE.
-------------------------------------------------------------------------------

with Ada.Real_Time;
with Ada.Interrupts;
with DecaDriver_Config;
with DW1000.Constants;
with DW1000.Driver;          use DW1000.Driver;
with DW1000.BSP;
with DW1000.Register_Types;
with Dw1000.Types;           use DW1000.Types;
with System;

package DecaDriver
with SPARK_Mode => On
is
   type Configuration_Type is record
      Channel             : DW1000.Driver.Channel_Number;
      PRF                 : DW1000.Driver.PRF_Type;
      Tx_Preamble_Length  : DW1000.Driver.Preamble_Lengths;
      Tx_PAC              : DW1000.Driver.Preamble_Acq_Chunk_Length;
      Tx_Preamble_Code    : DW1000.Driver.Preamble_Code_Number;
      Rx_Preamble_Code    : DW1000.Driver.Preamble_Code_Number;
      Use_Nonstandard_SFD : Boolean;
      Data_Rate           : DW1000.Driver.Data_Rates;
      PHR_Mode            : DW1000.Driver.Physical_Header_Modes;
      SFD_Timeout         : DW1000.Driver.SFD_Timeout_Number;
      Enable_Smart_Power  : Boolean;
   end record;

   subtype Frame_Length is Natural range 0 .. 1024;

   type Rx_Errors is (No_Error,
                      Frame_Timeout,
                      Preamble_Timeout,
                      SFD_Timeout,
                      RS_Error,
                      FCS_Error);

   type Rx_Frame_Type is record
      Size    : Frame_Length;
      Frame   : Byte_Array (Frame_Length);
      Error   : Rx_Errors;
      Overrun : Boolean;
   end record
     with Dynamic_Predicate => (if Rx_Frame_Type.Error = No_Error
                                then Rx_Frame_Type.Size > 0
                                else Rx_Frame_Type.Size = 0);

   type Rx_Frame_Queue_Index is mod 2;

   type Rx_Frame_Queue_Type is
     array (Rx_Frame_Queue_Index)
     of Rx_Frame_Type;

   type Tx_Power_Array is array (Natural range 0 .. 11) of Bits_32;

   protected type Receiver_Type
     with Interrupt_Priority => DecaDriver_Config.Driver_Priority
   is
      entry Wait (Frame   : in out Byte_Array;
                  Size    :    out Frame_Length;
                  Error   :    out Rx_Errors)
      with Depends => (Frame         => + Receiver_Type,
                       Size          => Receiver_Type,
                       Receiver_Type => Receiver_Type,
                       Error         => Receiver_Type),
        Pre => Frame'Length > 0,
        Post => (if Error = No_Error
                 then Size in 1 .. DW1000.Constants.RX_BUFFER_Length
                 else Size = 0);
      --  Waits for a frame to be received, or an error. When a frame is
      --  received (or if one has been previously received and is waiting to be
      --  read) then the frame's content and size are copied to the Frame and
      --  Size arguments.
      --
      --  If any of the enabled errors occurs (e.g. an FCS error is detected)
      --  then the Error argument is set to specify the type of receive error
      --  that occurred, Size is set to 0, and the contents of the Frame array
      --  are unmodified.
      --
      --  If no error occurs (Error is set to No_Error) then the frame contents
      --  are copied to the Frame array, and Size is set to the length of the
      --  frame (in bytes). If the Frame array is too small to store the
      --  received frame then the frame's contents are truncated, but the Size
      --  argument still reflects the frame's true size.
      --
      --  If the Frame array is larger than the received frame then the extra
      --  bytes in the Frame array are unmodified.

      function Pending_Frames_Count return Natural
        with Post => Pending_Frames_Count'Result <= 2;
      --  Returns the number of received frames that are waiting to be read.

      procedure Enable_Rx (Delayed : in     Boolean;
                           Result  :    out Result_Type)
        with Global => (In_Out => DW1000.BSP.Device_State),
        Depends => (DW1000.BSP.Device_State => + Delayed,
                    Result                  => (DW1000.BSP.Device_State, Delayed),
                    Receiver_Type           => Receiver_Type),
        Post => (if not Delayed then Result = Success);
      pragma Annotate
        (GNATprove, False_Positive,
         "potentially blocking operation in protected operation ""Enable_Rx""",
         "Procedures in DW1000.BSP are not blocking");


      procedure Notify_Frame_Received
        with Global => (In_Out => DW1000.BSP.Device_State),
        Depends => (DW1000.BSP.Device_State => + Receiver_Type,
                    Receiver_Type           => + DW1000.BSP.Device_State);
      pragma Annotate
        (GNATprove, False_Positive,
         "potentially blocking operation in protected operation ""Notify_Frame_Received""",
         "Procedures in DW1000.BSP are not blocking");


      --  Reads a received frame from the DW1000.
      --
      --  WARNING: This is intended to only be called by the DecaDriver IRQ
      --  when the DW1000 signals that a frame has been received. This procedure
      --  should not be called by the user.

      procedure Notify_Receive_Error (Error : in Rx_Errors)
        with Depends => (Receiver_Type => + Error),
        Pre => Error /= No_Error;

   private

      Frame_Queue : Rx_Frame_Queue_Type :=
                      (others => (Size    => 0,
                                  Frame   => (others => 0),
                                  Error   => No_Error,
                                  Overrun => False));
      --  Cyclic buffer for storing received frames, read from the DW1000.

      Queue_Head       : Rx_Frame_Queue_Index := 1;
      Rx_Count         : Natural              := 0;
      Overrun_Occurred : Boolean              := False;
      Frame_Ready      : Boolean              := False;
   end Receiver_Type;


   protected type Transmitter_Type
     with Interrupt_Priority => DecaDriver_Config.Driver_Priority
   is

      entry Wait_For_Tx_Complete;
      --  Wait for an in in-progress transmission to finish.
      --
      --  This entry blocks whilst the transmitter is busy sending a packet.
      --  Otherwise, when the transmitter is idle this entry does not block.

      function Is_Tx_Complete return Boolean;
      --  Check if the transmitter is busy.
      --
      --  Returns True when the transmitter is idle, and False otherwise.

      procedure Set_Tx_Data (Data   : in Byte_Array;
                             Offset : in Natural)
        with Global => (In_Out => DW1000.BSP.Device_State),
        Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                                Data,
                                                Offset),
                    Transmitter_Type        => Transmitter_Type),
        Pre => (Data'Length in 1 .. 1024 and then
                Offset < 1024            and then
                Data'Length + Offset <= 1024);
      pragma Annotate
        (GNATprove, False_Positive,
         "potentially blocking operation in protected operation ""Set_Tx_Data""",
         "Procedures in DW1000.BSP are not blocking");

      procedure Set_Tx_Frame_Length (Length : in Natural;
                                     Offset : in Natural)
        with Global => (In_Out => DW1000.BSP.Device_State),
        Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                                Length,
                                                Offset),
                    Transmitter_Type        => Transmitter_Type),
        Pre => (Length in 1 .. DW1000.Constants.TX_BUFFER_Length and then
                Offset < DW1000.Constants.TX_BUFFER_Length       and then
                Length + Offset <= DW1000.Constants.TX_BUFFER_Length);
      pragma Annotate
        (GNATprove, False_Positive,
         "potentially blocking operation in protected operation ""Set_Tx_Frame_Length""",
         "Procedures in DW1000.BSP are not blocking");

      procedure Start_Tx (Delayed_Tx  : in     Boolean;
                          Rx_After_Tx : in     Boolean;
                          Result      :    out DW1000.Driver.Result_Type)
        with Global => (In_Out => DW1000.BSP.Device_State),
        Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                                Delayed_Tx,
                                                Rx_After_Tx),
                    Result                  => (DW1000.BSP.Device_State,
                                                Delayed_Tx,
                                                Rx_After_Tx),
                    Transmitter_Type        => (Transmitter_Type,
                                                DW1000.BSP.Device_State,
                                                Delayed_Tx,
                                                Rx_After_Tx));
      pragma Annotate
        (GNATprove, False_Positive,
         "potentially blocking operation in protected operation ""Start_Tx""",
         "Procedures in DW1000.BSP are not blocking");

      procedure Notify_Tx_Complete;
      --  Notify the driver that the transmit is complete.
      --
      --  WARNING: This procedure is intended to be called only by the DW1000
      --  IRQ. This procedure should not be called by the user.

   private
      Tx_Idle : Boolean := True;
      --  True when the transmitter is idle, False otherwise.

   end Transmitter_Type;

   Receiver    : Receiver_Type;
   Transmitter : Transmitter_Type;

   protected type Driver_Type
     with Interrupt_Priority => DecaDriver_Config.Driver_Priority
   is

      procedure Initialize (Load_Antenna_Delay   : in Boolean;
                            Load_XTAL_Trim       : in Boolean;
                            Load_Tx_Power_Levels : in Boolean;
                            Load_UCode_From_ROM  : in Boolean)
        with Global => (In_Out => DW1000.BSP.Device_State),
        Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                                Driver_Type,
                                                Load_Antenna_Delay,
                                                Load_XTAL_Trim,
                                                Load_Tx_Power_Levels,
                                                Load_UCode_From_ROM),
                    Driver_Type             => + (DW1000.BSP.Device_State,
                                                  Load_Antenna_Delay,
                                                  Load_XTAL_Trim,
                                                  Load_Tx_Power_Levels,
                                                  Load_UCode_From_ROM));
      --  Initialize the DecaDriver and DW1000.
      --
      --  If Load_Antenna_Delay is True then the antenna delay is read from the
      --  DW1000 OTP memory and is stored in this DecaDriver. The antenna delay
      --  is applied when the Configure procedure is called.
      --
      --  If Load_XTAL_Trim is True then the XTAL trim is read from the DW1000
      --  OTP memory and is stored in this DecaDriver. The XTAL trim is applied
      --  when the Configure procedure is called.
      --
      --  If Load_Tx_Power_Levels is True then the transmit power levels are
      --  read from the DW1000 OTP memory and is stored in this DecaDriver. The
      --  transmit power levels are applied when the Configure procedure is
      --  called, based on the specific configuration (channel & PRF).
      --
      --  If Load_UCode_From_ROM is True then the LDE microcode is loaded from
      --  the DW1000's ROM into the DW1000's RAM. This is necessary for the LDE
      --  algorithm to operate. If this is False then the LDE algorithm is
      --  disabled and is not run when packets are received.
      pragma Annotate
        (GNATprove, False_Positive,
         "potentially blocking operation in protected operation ""Initialize""",
         "Procedures in DW1000.BSP are not blocking");

      procedure Configure (Config : in Configuration_Type)
        with Global => (In_Out => DW1000.BSP.Device_State),
        Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                                Config,
                                                Driver_Type),
                    Driver_Type             => + Config),
        Post => (PHR_Mode = Config.PHR_Mode);
      --  Configure the DW1000 for a specific channel, PRF, preamble, etc...
      pragma Annotate
        (GNATprove, False_Positive,
         "potentially blocking operation in protected operation ""Configure""",
         "Procedures in DW1000.BSP are not blocking");


      procedure Configure_Errors (Frame_Timeout : in Boolean;
                                  SFD_Timeout   : in Boolean;
                                  PHR_Error     : in Boolean;
                                  RS_Error      : in Boolean;
                                  FCS_Error     : in Boolean)
        with Global => (In_Out => DW1000.BSP.Device_State),
        Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                                Frame_Timeout,
                                                SFD_Timeout,
                                                PHR_Error,
                                                RS_Error,
                                                FCS_Error),
                    Driver_Type             => (Driver_Type,
                                                Frame_Timeout,
                                                SFD_Timeout,
                                                PHR_Error,
                                                RS_Error,
                                                FCS_Error));
      pragma Annotate
        (GNATprove, False_Positive,
         "potentially blocking operation in protected operation ""Configure_Errors""",
         "Procedures in DW1000.BSP are not blocking");

      function Get_Part_ID return Bits_32;
      function Get_Lot_ID  return Bits_32;

      function PHR_Mode return DW1000.Driver.Physical_Header_Modes
        With Depends => (PHR_Mode'Result => Driver_Type);

   private

      procedure DW1000_IRQ
        with Attach_Handler => DecaDriver_Config.DW1000_IRQ_Id,
        Global => (In_Out => (DW1000.BSP.Device_State,
                              Receiver,
                              Transmitter)),
        Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                                Driver_Type,
                                                Receiver),
                    Driver_Type             => Driver_Type,
                    Transmitter             => (DW1000.BSP.Device_State,
                                                Transmitter,
                                                Driver_Type),
                    Receiver                => (DW1000.BSP.Device_State,
                                                Receiver,
                                                Driver_Type));
      pragma Annotate
        (GNATprove, False_Positive,
         "potentially blocking operation in protected operation ""DW1000_IRQ""",
         "Procedures in DW1000.BSP are not blocking");
      --  DW1000 IRQ handler.
      --
      --  This performs functionality for packet reception and transmission.

      Part_ID : Bits_32 := 0;
      Lot_ID  : Bits_32 := 0;

      Antenna_Delay_PRF_64 : Bits_16 := 0;
      Antenna_Delay_PRF_16 : Bits_16 := 0;
      XTAL_Trim            : Bits_5  := 2#1_0000#;

      OTP_Tx_Power_Levels  : Tx_Power_Array := (others => 0);

      Long_Frames : Boolean := False;

      SYS_CFG_Reg : DW1000.Register_Types.SYS_CFG_Type :=
                      DW1000.Register_Types.SYS_CFG_Type'
                        (FFEN       => 0,
                         FFBC       => 0,
                         FFAB       => 0,
                         FFAD       => 0,
                         FFAA       => 0,
                         FFAM       => 0,
                         FFAR       => 0,
                         FFA4       => 0,
                         FFA5       => 0,
                         HIRQ_POL   => 0,
                         SPI_EDGE   => 0,
                         DIS_FCE    => 0,
                         DIS_DRXB   => 0,
                         DIS_PHE    => 0,
                         DIS_RSDE   => 0,
                         FCS_INT2F  => 0,
                         PHR_MODE   => 0,
                         DIS_STXP   => 0,
                         RXM110K    => 0,
                         RXWTOE     => 0,
                         RXAUTR     => 0,
                         AUTOACK    => 0,
                         AACKPEND   => 0,
                         Reserved_1 => 0,
                         Reserved_2 => 0);

      Use_OTP_XTAL_Trim     : Boolean := False;
      Use_OTP_Antenna_Delay : Boolean := False;

      Detect_Frame_Timeout  : Boolean := False;
      Detect_SFD_Timeout    : Boolean := False;
      Detect_PHR_Error      : Boolean := False;
      Detect_RS_Error       : Boolean := False;
      Detect_FCS_Error      : Boolean := False;

   end Driver_Type;

   Driver      : Driver_Type;

end DecaDriver;
