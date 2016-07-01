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

pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

with DW1000.Constants;
with DW1000.BSP;
with DW1000.Types;      use DW1000.Types;
with Interfaces;        use Interfaces;

--  This package contains high-level procedures for using the DW1000.
package DW1000.Driver
with SPARK_Mode => On
is
   type Result_Type is
     (Success,
      Error);

   type Clocks is
     (Enable_All_Seq,
      Force_Sys_XTI,
      Force_Sys_PLL,
      Read_Acc_On,
      Read_Acc_Off,
      Force_OTP_On,
      Force_OTP_Off,
      Force_Tx_PLL);

   type Data_Rates is
     (Data_Rate_110k,  -- 110 kbps
      Data_Rate_850k,  -- 850 kbps
      Data_Rate_6M8); -- 6.8 Mbps
   for Data_Rates use
     (Data_Rate_110k => 2#00#,
      Data_Rate_850k => 2#01#,
      Data_Rate_6M8  => 2#10#);

   type Channel_Number is range 1 .. 7
     with Static_Predicate => Channel_Number in 1..5 | 7;
   --  Channels 1 .. 5 and 7 are supported by the DW1000.

   type PRF_Type is (PRF_16MHz, PRF_64MHz);
   for PRF_Type use
     (PRF_16MHz => 2#01#,
      PRF_64MHz => 2#10#);

   type Preamble_Lengths is
     (PLEN_64,
      PLEN_128,
      PLEN_256,
      PLEN_512,
      PLEN_1024,
      PLEN_1536,
      PLEN_2048,
      PLEN_4096);

   type Preamble_Acq_Chunk_Length is
     (PAC_8,
      PAC_16,
      PAC_32,
      PAC_64);

   type Preamble_Code_Number is new Positive range 1 .. 24;

   type Physical_Header_Modes is
     (Standard_Frames,
      Extended_Frames);
   for Physical_Header_Modes use
     (Standard_Frames => 2#00#,
      Extended_Frames => 2#11#);

   type SFD_Timeout_Number is new Natural range 0 .. (2**16) - 1;

   type Rx_Modes is (Normal, Sniff);


   procedure Load_LDE_From_ROM
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => DW1000.BSP.Device_State);
   --  Loads the leading edge detection (LDE) microcode from ROM.
   --
   --  The LDE code must be loaded in order to use the LDE algorithm. If the
   --  LDE code is not loaded then the LDERUNE bit in the PMSC_CTRL1 register
   --  must be set to 0.
   --
   --  Note: This procedure modifies the clocks setting in PMSC_CTRL0.

   procedure Enable_Clocks (Clock : in Clocks)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Clock);
   --  Enables and configures the specified clock.
   --
   --  This procedure configures the following registers:
   --    * PMSC_CTRL0

   procedure Read_OTP (Address : in     Bits_11;
                       Word    :    out Bits_32)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => ((DW1000.BSP.Device_State, Word) => (DW1000.BSP.Device_State, Address));
   --  Reads a 32-bit word from the DW1000 one-time programmable (OTP) memory.
   --
   --  The package DW1000.Constants defines the addresses used to store the
   --  various data stored in the OTP memory.

   procedure Read_Extended_Unique_Identifier (EUI_Value : out Bits_64)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => ((DW1000.BSP.Device_State,
                 EUI_Value) => DW1000.BSP.Device_State);
   --  Read the extended unique identified (EUID).

   procedure Read_Tx_Antenna_Delay (Antenna_Delay : out Bits_16)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => ((DW1000.BSP.Device_State,
                 Antenna_Delay) => DW1000.BSP.Device_State);
   --  Read the currently configured Tx antenna delay.
   --
   --  The antenna delay is a 16-bit value using the same unit as the system
   --  time and time stamps, i.e. 499.2 MHz * 128, so the least significant
   --  bit is approximately 15.65 picoseconds.

   procedure Write_Tx_Antenna_Delay (Antenna_Delay : in Bits_16)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                             Antenna_Delay));
   --  Set the Tx antenna delay.
   --
   --  The antenna delay is a 16-bit value using the same unit as the system
   --  time and time stamps, i.e. 499.2 MHz * 128, so the least significant
   --  bit is approximately 15.65 picoseconds.
   --
   --  This procedure configures the following registers:
   --    * TX_ANTD

   procedure Read_Rx_Antenna_Delay (Antenna_Delay : out Bits_16)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => ((DW1000.BSP.Device_State,
                 Antenna_Delay) => DW1000.BSP.Device_State);
   --  Read the currently configured Rx antenna delay.
   --
   --  The antenna delay is a 16-bit value using the same unit as the system
   --  time and time stamps, i.e. 499.2 MHz * 128, so the least significant
   --  bit is approximately 15.65 picoseconds.

   procedure Write_Rx_Antenna_Delay (Antenna_Delay : in Bits_16)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                             Antenna_Delay));
   --  Set the Rx antenna delay.
   --
   --  The antenna delay is a 16-bit value using the same unit as the system
   --  time and time stamps, i.e. 499.2 MHz * 128, so the least significant
   --  bit is approximately 15.65 picoseconds.
   --
   --  This procedure configures the following registers:
   --    * LDE_RXANTD

   procedure Configure_LDE (PRF : in PRF_Type)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State, PRF));
   --  Configures the LDE subsystem for the specified pulse repetition
   --  frequency (PRF).
   --
   --  This procedure configures the following registers:
   --    * LDE_CFG1
   --    * LDE_CFG2

   procedure Configure_PLL (Channel : in Channel_Number)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                             Channel));
   --  Configures the PLL subsystem for the specified UWB channel.
   --
   --  This procedure configures the following registers:
   --    * FS_PLLCFG
   --    * FS_PLLTUNE
   --    * FS_XTALT

   procedure Configure_RF (Channel : in Channel_Number)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                             Channel));
   --  Configures the RF subsystem for the specified UWB channel.
   --
   --  This procedure configures the following registers:
   --    * RF_RXCTRLH
   --    * RF_TXCTRL

   procedure Configure_DRX (PRF                : in PRF_Type;
                            Data_Rate          : in Data_Rates;
                            Tx_Preamble_Length : in Preamble_Lengths;
                            PAC                : in Preamble_Acq_Chunk_Length;
                            SFD_Timeout        : in SFD_Timeout_Number;
                            Nonstandard_SFD    : in Boolean)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State
                 => (DW1000.BSP.Device_State,
                     PRF,
                     Data_Rate,
                     Tx_Preamble_Length,
                     PAC,
                     SFD_Timeout,
                     Nonstandard_SFD));
   --  Configures the DRX subsystem for the specified configuration.
   --
   --  This procedure configures the following registers:
   --    * DRX_TUNE0b
   --    * DRX_TUNE1a
   --    * DRX_TUNE1b
   --    * DRX_TUNE4H
   --    * DRX_TUNE2
   --    * DRX_SFDTOC

   procedure Configure_AGC (PRF : in PRF_Type)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + PRF);
   --  Configures the automatic gain control (AGC) subsystem.
   --
   --  This procedure configures the following registers:
   --    * AGC_TUNE2
   --    * AGC_TUNE1

   procedure Configure_Nonstandard_SFD_Length (Data_Rate : in Data_Rates)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Data_Rate);
   --  Configures the length of the non-standard SFD for the specified
   --  data rate.
   --
   --  This procedure configures the following registers:
   --    * USR_SFD

   procedure Set_Smart_Tx_Power (Enabled : in Boolean)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Enabled);
   --  Enables or disables smart Tx power control.
   --
   --  Regulations for UWB typically specify a maximum transmit power limit of
   --  -41.3 dBm / MHz, typically measured with a dwell time of 1 ms. Short
   --  frames transmitted at a data rate of 6.8 Mbps and a short preamble
   --  length are transmitted in a fraction of a millisecond. If only a single
   --  short frame is transmitted with in 1 ms then the frame can be
   --  transmitted at a higher power than the -41.3 dBm / MHz regulatory limit.
   --
   --  When the smart tx power control is enabled then the DW1000 will
   --  boost the power for short transmissions. It is the user's responsibility
   --  to avoid sending multiple short frames within the same millisecond to
   --  remain within the regulatory limits.
   --
   --  This procedure configures the following registers:
   --    * SYS_CFG

   procedure Set_Tx_Data (Data   : in Types.Byte_Array;
                          Offset : in Natural)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State
                 => (DW1000.BSP.Device_State,
                     Data,
                     Offset)),
     Pre =>
       (Data'Length > 0
        and then Data'Length <= DW1000.Constants.TX_BUFFER_Length
        and then Offset < DW1000.Constants.TX_BUFFER_Length
        and then Data'Length + Offset <= DW1000.Constants.TX_BUFFER_Length);
   --  Write data to the DW1000 TX buffer.
   --
   --  Before starting the transmission, the frame length and offset must be
   --  programmed into the DW1000 separately using the Set_Tx_Frame_Length
   --  procedure.
   --
   --  The frame is not transmitted until the Start_Tx procedure is called.
   --
   --  This procedure configures the following registers:
   --    * TX_BUFFER

   procedure Set_Tx_Frame_Length (Length : in Natural;
                                  Offset : in Natural)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + (Length, Offset)),
     Pre => (Length < DW1000.Constants.TX_BUFFER_Length
             and then Offset < DW1000.Constants.TX_BUFFER_Length
             and then Length + Offset <= DW1000.Constants.TX_BUFFER_Length);
   --  Configures the frame length and offset within the transmit buffer
   --  (TX_BUFFER) to use when transmitting the next packet.
   --
   --  This procedure configures the following registers:
   --    * TX_FCTRL

   procedure Read_Rx_Data (Data   :    out Types.Byte_Array;
                           Offset : in     Natural)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + (Offset, Data),
                 Data                    => (DW1000.BSP.Device_State, Offset)),
     Pre =>
       (Data'Length > 0
        and then Data'Length <= DW1000.Constants.RX_BUFFER_Length
        and then Offset < DW1000.Constants.RX_BUFFER_Length
        and then Data'Length + Offset <= DW1000.Constants.RX_BUFFER_Length);
   --  Read the received frame from the Rx buffer.

   procedure Start_Tx (Delayed_Tx  : in     Boolean;
                       Rx_After_Tx : in     Boolean;
                       Result      :    out Result_Type)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + (Delayed_Tx, Rx_After_Tx),
                 Result                  => (DW1000.BSP.Device_State,
                                             Delayed_Tx,
                                             Rx_After_Tx));
   --  Transmit the contents of the TX buffer.
   --
   --  When Delayed_Tx is False then the packet is transmitted immediately
   --  without delay. When Delayed_Tx is false then the transmit is delayed
   --  for the currently configured delay time. The delay time can be set
   --  using the Set_Tx_Rx_Delay_Time procedure.
   --
   --  When Rx_After_Tx is True then the receiver is automatically enabled
   --  after the transmission is completed.
   --
   --  This procedure configures the following registers:
   --    * SYS_CTRL

   procedure Set_Tx_Rx_Delay_Time (Delay_Time : in Types.Bits_40)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Delay_Time);
   --  Set the receive and transmit delay.
   --
   --  Both Rx and Tx share the same delay. It is not possible for the receiver
   --  and transmitter to use different delays simultaneously.
   --
   --  The delay time is measured in units of 499.2 MHz * 128, i.e. the least
   --  significant bit of the delay time is approximately 15.65 ps.
   --
   --  This procedure configures the following registers:
   --    * DX_TIME

   procedure Set_Sleep_After_Tx (Enabled : in Boolean)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Enabled);
   --  Configures the DW1000 to enter sleep more (or not) after transmitting a
   --  frame.
   --
   --  When Enable is True, the DW1000 will automatically enter sleep mode
   --  after each frame is sent. Otherwise, when Enable is False the DW1000
   --  will not enter sleep mode after each frame is sent.
   --
   --  This procedure configures the following registers:
   --    * PMSC_CTRL1

   procedure Read_Rx_Timestamp (Timestamp : out Types.Bits_40)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => DW1000.BSP.Device_State,
                 Timestamp               => DW1000.BSP.Device_State);
   --  Read the 40-bit timestamp associated with the last received packet.
   --
   --  The timestamp is measured in units of 499.2 MHz * 128, i.e. the least
   --  significant bit of the timestamp is approximately 15.65 ps.

   procedure Read_Tx_Timestamp (Timestamp : out Types.Bits_40)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => DW1000.BSP.Device_State,
                 Timestamp               => DW1000.BSP.Device_State);
   --  Read the 40-bit timestamp associated with the last transmitted packet.
   --
   --  The timestamp is measured in units of 499.2 MHz * 128, i.e. the least
   --  significant bit of the timestamp is approximately 15.65 ps.

   procedure Read_System_Timestamp (Timestamp : out Types.Bits_40)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => DW1000.BSP.Device_State,
                 Timestamp               => DW1000.BSP.Device_State);
   --  Read the current value of the DW1000's system timestamp.
   --
   --  The timestamp is measured in units of 499.2 MHz * 128, i.e. the least
   --  significant bit of the timestamp is approximately 15.65 ps.

   procedure Check_Overrun (Overrun : out Boolean)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => DW1000.BSP.Device_State,
                 Overrun                 => DW1000.BSP.Device_State);
   --  Check if an overrun condition has occurred.
   --
   --  An overrun condition occurs if the DW1000 receives a new packet before
   --  the host processor has been able to read the previously received packet.
   --
   --  See Section 4.3.5 of the DW1000 User Manual for more information of the
   --  overrun condition.

   procedure Force_Tx_Rx_Off
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => DW1000.BSP.Device_State);
   --  Force off the tranceiver.
   --
   --  This also clears the status registers.

   procedure Sync_Rx_Buffer_Pointers
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => DW1000.BSP.Device_State);
   --  Synchronize the Rx buffer pointers for double-buffer operation.
   --
   --  This procedure synchronizes the ICRBP and HSRBP bits in the SYS_CTRL
   --  register so that they are the same. This is only relevant when the
   --  DW1000 is operating in double-buffer mode.
   --
   --  This procedure configures the following registers:
   --    * SYS_CTRL

   procedure Enable_Rx (Delayed : in     Boolean;
                        Result  :    out Result_Type)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Delayed,
                 Result                  => (DW1000.BSP.Device_State,
                                             Delayed)),
     Post => (if not Delayed then Result = Success);
   --  Enable the receiver.
   --
   --  If Delayed is set to True then the receiver is enabled only after the
   --  delay configured by the Set_Tx_Rx_Delay_Time procedure after this
   --  procedure is called.
   --
   --  This procedure configures the following registers:
   --    * SYS_CTRL

   procedure Set_Rx_Mode (Mode        : in Rx_Modes;
                          Rx_On_Time  : in Types.Bits_4;
                          Rx_Off_Time : in Types.Bits_8)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + (Mode, Rx_On_Time, Rx_Off_Time)),
     Pre => (if Mode = Sniff then Rx_Off_Time > 0);
   --  Enables or disables the receiver sniff mode.
   --
   --  When Mode is set to Normal then when the receiver is turned on (see
   --  the Enable_Rx procedure) then it will operate until either a frame is
   --  received, or until the receiver timeout time is reached. In the Normal
   --  mode the Rx_On_Time and Rx_Off_Time parameters are not used.
   --
   --  When Mode is set to Sniff then the receiver will be activated for the
   --  duration of the Rx_On_Time, searching for a preamble. If a preamble is
   --  detected within this duration then the receiver continues operation to
   --  try to receive the packet. Otherwise, if no preamble is detected then
   --  the receiver is then disabled for the Rx_Off_Time, after which it is
   --  re-enabled to repeat the process.
   --
   --  The Rx_On_Time is measured in units of the preamble accumulation count
   --  (PAC) see Section 4.1.1 of the DW100 User Manual for more information.
   --
   --  The Rx_Off_Time is measured in units of the 128 system clock cycles, or
   --  approximately 1 us. If the Mode is set to Sniff then the Rx_Off_Time
   --  must be non-zero (a value of 0 would disable the sniff mode on the
   --  DW1000).
   --
   --  This procedure configures the following registers:
   --    * RX_SNIFF

   procedure Set_Auto_Rx_Reenable (Enabled : in Boolean)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Enabled);
   --  Configures the receiver to automatically re-enable after frame reception
   --
   --  When the auto Rx re-enable is enabled the receiver will automatically
   --  re-enable itself after each frame is received. This is useful when
   --  using double-buffer mode.
   --
   --  This procedure configures the following registers:
   --    * SYS_CFG

   procedure Set_Rx_Double_Buffer (Enabled : in Boolean)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Enabled);
   --  Configures double-buffer mode.
   --
   --  By default the DW1000 operates in single-buffer mode. Double-buffer
   --  mode can be enabled to allow the host application to read the previously
   --  received frame at the same time as the DW1000 is receiving the next
   --  frame.
   --
   --  Also see the Sync_Rx_Buffer_Pointers procedure.
   --
   --  This procedure configures the following registers:
   --    * SYS_CFG

   procedure Set_Rx_Timeout (Timeout : in Types.Bits_16)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Timeout);
   --  Configure the receive timeout.
   --
   --  When the receiver is enabled the receive timeout is started.
   --  If no complete frame is received within the configured Rx timeout
   --  then the receiver is automatically disabled.
   --
   --  The Rx timeout can be disabled by setting the Timeout to 0.
   --
   --  The Rx timeout is measured in units of 499.2 MHz / 512, i.e. the least
   --  significant bit is approximately 1.026 us.
   --
   --  This procedure configures the following registers:
   --    * SYS_CFG

   procedure Set_Preamble_Detect_Timeout (Timeout : in Types.Bits_16)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Timeout);
   --  Configure the preamble detection timeout.
   --
   --  When the receiver is enabled the preamble timeout is started.
   --  If no preamble is detected within the configured preamble detection
   --  timeout then the receiver is automatically disabled.
   --
   --  The preamble detect timeout can be disabled by setting the Timeout to 0.
   --
   --  The preamble detect timeout is measured in units of preamble acquisition
   --  chunk (PAC) size, which can be 8, 16, 32, or 64. See Section 7.2.40.9 of
   --  the DW1000 User Manual for more information.
   --
   --  This procedure configures the following registers:
   --    * DRX_PRETOC

   procedure Calibrate_Sleep_Count
     (Half_XTAL_Cycles_Per_LP_Osc_Cycle : out Types.Bits_16)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State           => DW1000.BSP.Device_State,
                 Half_XTAL_Cycles_Per_LP_Osc_Cycle => DW1000.BSP.Device_State);

   procedure Upload_AON_Config
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => DW1000.BSP.Device_State);
   --  Upload the AON block configurations to the AON.
   --
   --  This uploads the configuration from the AON_CFG0 and AON_CFG1 registers
   --  into the AON block.

   procedure Save_Registers_To_AON
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => DW1000.BSP.Device_State);
   --  Copy the user configurations from the host interface register set into
   --  the AON memory.
   --
   --  If enabled to do so, after exiting sleep mode the DW1000 will reload the
   --  user configuration from the AON memory into the host interface register
   --  set.
   --
   --  The behaviour of the AON subsystem when exiting sleep or deep-sleep
   --  states can be configured via the AON_WCFG register.

   procedure Restore_Registers_From_AON
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => DW1000.BSP.Device_State);
   --  Load the user configuration from the AON memory into the host interface
   --  register set.

   procedure AON_Read_Byte (Address : in     Types.Bits_8;
                            Data    :    out Types.Bits_8)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends =>
       (DW1000.BSP.Device_State => (DW1000.BSP.Device_State, Address),
        Data                    => (DW1000.BSP.Device_State, Address));
   -- Reads a single byte from the Always-On block.

   procedure AON_Contiguous_Read (Start_Address : in     Types.Bits_8;
                                  Data          :    out Types.Byte_Array)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                             Start_Address,
                                             Data),
                 Data                    => + (DW1000.BSP.Device_State,
                                               Start_Address)),
     Pre => (Data'Length <= 256
             and then Natural (Start_Address) + Data'Length <= 256);
   -- Reads a contiguous sequence of bytes from the Always-On block.

   procedure AON_Scatter_Read (Addresses : in     Types.Byte_Array;
                               Data      :    out Types.Byte_Array)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                             Addresses,
                                             Data),
                 Data                    => + (DW1000.BSP.Device_State,
                                               Addresses)),
     Pre => Addresses'Length = Data'Length;
   --  Reads a non-contiguous set of bytes from the Always-on block.
   --
   --  This procedure reads bytes from the sequence of addresses in the
   --  Addresses array, and stores the byte that was read in the corresponding
   --  position in the Data array.

   procedure Configure_Sleep_Count (Sleep_Count : in Types.Bits_16)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Sleep_Count);

   procedure Set_XTAL_Trim (Trim : in Types.Bits_5)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Trim);

   procedure Configure_LEDs (Tx_LED_Enable    : in Boolean;
                             Rx_LED_Enable    : in Boolean;
                             Rx_OK_LED_Enable : in Boolean;
                             SFD_LED_Enable   : in Boolean;
                             Test_Flash       : in Boolean)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => (DW1000.BSP.Device_State,
                                             Tx_LED_Enable,
                                             Rx_LED_Enable,
                                             Rx_OK_LED_Enable,
                                             SFD_LED_Enable,
                                             Test_Flash));

end DW1000.Driver;
