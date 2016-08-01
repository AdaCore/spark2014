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

with DW1000.Constants;
with DW1000.Registers;
with DW1000.Register_Driver;
with Interfaces; use Interfaces;

package body DecaDriver
with SPARK_Mode => On
is
   Default_SFD_Timeout : constant DW1000.Driver.SFD_Timeout_Number := 16#1041#;

   LDE_Replica_Coeffs : constant
     array (DW1000.Driver.Preamble_Code_Number) of Bits_16
       := (1  => Bits_16 (0.35 * 2**16),
           2  => Bits_16 (0.35 * 2**16),
           3  => Bits_16 (0.32 * 2**16),
           4  => Bits_16 (0.26 * 2**16),
           5  => Bits_16 (0.27 * 2**16),
           6  => Bits_16 (0.18 * 2**16),
           7  => Bits_16 (0.50 * 2**16),
           8  => Bits_16 (0.32 * 2**16),
           9  => Bits_16 (0.16 * 2**16),
           10 => Bits_16 (0.20 * 2**16),
           11 => Bits_16 (0.23 * 2**16),
           12 => Bits_16 (0.24 * 2**16),
           13 => Bits_16 (0.23 * 2**16),
           14 => Bits_16 (0.21 * 2**16),
           15 => Bits_16 (0.27 * 2**16),
           16 => Bits_16 (0.21 * 2**16),
           17 => Bits_16 (0.20 * 2**16),
           18 => Bits_16 (0.21 * 2**16),
           19 => Bits_16 (0.21 * 2**16),
           20 => Bits_16 (0.28 * 2**16),
           21 => Bits_16 (0.23 * 2**16),
           22 => Bits_16 (0.22 * 2**16),
           23 => Bits_16 (0.19 * 2**16),
           24 => Bits_16 (0.22 * 2**16));


   protected body Receiver_Type
   is
      entry Wait (Frame : in out DW1000.Types.Byte_Array;
                  Size  :    out Frame_Length;
                  Error :    out Rx_Errors)
        when Frame_Ready
      is
      begin
         Size  := Frame_Queue (Queue_Head).Size;
         Error := Frame_Queue (Queue_Head).Error;

         if Error = No_Error then
            if Frame'Length >= Size then
               Frame (Frame'First .. Frame'First + Integer (Size - 1))
                 := Frame_Queue (Queue_Head).Frame (1 .. Size);

            else
               Frame := Frame_Queue (Queue_Head).Frame (1 .. Frame'Length);

            end if;
         end if;

         Queue_Head  := Queue_Head + 1;
         Rx_Count    := Rx_Count - 1;
         Frame_Ready := Rx_Count > 0;

      end Wait;

      function Pending_Frames_Count return Natural
      is
      begin
         return Rx_Count;
      end Pending_Frames_Count;

      procedure Enable_Rx (Delayed : in     Boolean;
                           Result  :    out Result_Type)
      is
      begin
         DW1000.Driver.Enable_Rx (Delayed => Delayed,
                                  Result  => Result);
      end Enable_Rx;

      procedure Notify_Frame_Received
      is
         RX_FINFO_Reg : DW1000.Register_Types.RX_FINFO_Type;

         Frame_Length : Natural;
         Next_Idx     : Rx_Frame_Queue_Index;

      begin
         --  Read the frame length from the DW1000
         DW1000.Registers.RX_FINFO.Read (RX_FINFO_Reg);
         Frame_Length := Natural (RX_FINFO_Reg.RXFLEN) +
                         Natural (RX_FINFO_Reg.RXFLE) * 2**7;

         pragma Assert (Frame_Length <= 1024);

         if Frame_Length > 0 then
            if Rx_Count >= Frame_Queue'Length then
               Overrun_Occurred := True;

            else
               Next_Idx := Queue_Head + Rx_Frame_Queue_Index (Rx_Count);

               Rx_Count := Rx_Count + 1;

               DW1000.Register_Driver.Read_Register
                 (Register_ID => DW1000.Registers.RX_BUFFER_Reg_ID,
                  Sub_Address => 0,
                  Data        =>
                    Frame_Queue (Next_Idx).Frame (1 .. Frame_Length));

               Frame_Queue (Next_Idx).Size    := Frame_Length;
               Frame_Queue (Next_Idx).Error   := No_Error;
               Frame_Queue (Next_Idx).Overrun := Overrun_Occurred;
               Overrun_Occurred := False;
            end if;

            Frame_Ready := True;
         end if;
      end Notify_Frame_Received;

      procedure Notify_Receive_Error (Error : in Rx_Errors)
      is
         Next_Idx     : Rx_Frame_Queue_Index;

      begin
         if Rx_Count >= Frame_Queue'Length then
            Overrun_Occurred := True;

         else
            Next_Idx := Queue_Head + Rx_Frame_Queue_Index (Rx_Count);

            Rx_Count := Rx_Count + 1;

            Frame_Queue (Next_Idx).Size    := 0;
            Frame_Queue (Next_Idx).Error   := Error;
            Frame_Queue (Next_Idx).Overrun := Overrun_Occurred;
            Overrun_Occurred := False;
         end if;

         Frame_Ready := True;
      end Notify_Receive_Error;

   end Receiver_Type;


   protected body Transmitter_Type
   is

      entry Wait_For_Tx_Complete
      with SPARK_Mode => Off --  Workaround for "statement has no effect" below
        when Tx_Idle
      is
      begin
         null;
      end Wait_For_Tx_Complete;

      function Is_Tx_Complete return Boolean
      is
      begin
         return Tx_Idle;
      end Is_Tx_Complete;

      procedure Set_Tx_Data (Data   : in DW1000.Types.Byte_Array;
                             Offset : in Natural)
      is
      begin
         DW1000.Driver.Set_Tx_Data (Data   => Data,
                                    Offset => Offset);
      end Set_Tx_Data;

      procedure Set_Tx_Frame_Length (Length : in Natural;
                                     Offset : in Natural)
      is
      begin
         DW1000.Driver.Set_Tx_Frame_Length (Length => Length,
                                            Offset => Offset);
      end Set_Tx_Frame_Length;

      procedure Start_Tx (Delayed_Tx  : in     Boolean;
                          Rx_After_Tx : in     Boolean;
                          Result      :    out DW1000.Driver.Result_Type)
      is
      begin
         DW1000.Driver.Start_Tx (Delayed_Tx  => Delayed_Tx,
                                 Rx_After_Tx => Rx_After_Tx,
                                 Result      => Result);

         Tx_Idle := not (Result = DW1000.Driver.Success);
      end Start_Tx;

      procedure Notify_Tx_Complete
      is
      begin
         Tx_Idle := True;
      end Notify_Tx_Complete;

   end Transmitter_Type;


   --  Driver_Type body

   protected body Driver_Type
   is

      procedure Initialize (Load_Antenna_Delay   : in Boolean;
                            Load_XTAL_Trim       : in Boolean;
                            Load_Tx_Power_Levels : in Boolean;
                            Load_UCode_From_ROM  : in Boolean)
      is
         Word : Bits_32;

         PMSC_CTRL1_Reg : DW1000.Register_Types.PMSC_CTRL1_Type;
         SYS_MASK_Reg   : DW1000.Register_Types.SYS_MASK_Type;

      begin

         DW1000.Driver.Enable_Clocks (DW1000.Driver.Force_Sys_XTI);

         DW1000.Driver.Read_OTP (DW1000.Constants.OTP_ADDR_CHIP_ID, Part_ID);
         DW1000.Driver.Read_OTP (DW1000.Constants.OTP_ADDR_LOT_ID, Lot_ID);

         if Load_Antenna_Delay then
            DW1000.Driver.Read_OTP (DW1000.Constants.OTP_ADDR_ANTENNA_DELAY,
                                    Word);

            -- High 16 bits are the antenna delay with a 64 MHz PRF.
            -- Low 16 bits are the antenna delay with a 16 MHz PRF.
            Antenna_Delay_PRF_16 := Bits_16 (Word and 16#FFFF#);
            Word := Shift_Right (Word, 16);
            Antenna_Delay_PRF_64 := Bits_16 (Word and 16#FFFF#);
         else
            Antenna_Delay_PRF_16 := 0;
            Antenna_Delay_PRF_64 := 0;
         end if;

         if Load_XTAL_Trim then
            DW1000.Driver.Read_OTP (DW1000.Constants.OTP_ADDR_XTAL_TRIM, Word);
            XTAL_Trim := Bits_5 (Word and 2#1_1111#);
         else
            XTAL_Trim := 2#1_0000#; -- Set to midpoint
         end if;

         if Load_Tx_Power_Levels then
            for I in OTP_Tx_Power_Levels'Range loop
               DW1000.Driver.Read_OTP (Bits_11 (16#10# + I),
                                      OTP_Tx_Power_Levels (I));
            end loop;

         else
            OTP_Tx_Power_Levels := (others => 0);
         end if;

         if Load_UCode_From_ROM then
            DW1000.Driver.Load_LDE_From_ROM;

         else
            -- Should disable LDERUN bit, since the LDE isn't loaded.
            DW1000.Registers.PMSC_CTRL1.Read (PMSC_CTRL1_Reg);
            PMSC_CTRL1_Reg.LDERUNE := 0;
            DW1000.Registers.PMSC_CTRL1.Write (PMSC_CTRL1_Reg);
         end if;

         DW1000.Driver.Enable_Clocks (DW1000.Driver.Force_Sys_PLL);
         DW1000.Driver.Enable_Clocks (DW1000.Driver.Enable_All_Seq);

         --  Store a local copy of the SYS_CFG register
         DW1000.Registers.SYS_CFG.Read (SYS_CFG_Reg);

         --  Configure IRQs
         DW1000.Registers.SYS_MASK.Read (SYS_MASK_Reg);
         SYS_MASK_Reg.MRXSFDTO := 0;
         SYS_MASK_Reg.MRXPHE   := 0;
         SYS_MASK_Reg.MRXRFSL  := 0;
         SYS_MASK_Reg.MRXFCE   := 0;
         SYS_MASK_Reg.MRXDFR   := 1; --  Always detect frame received
         SYS_MASK_Reg.MTXFRS   := 1; --  Always detect frame sent
         DW1000.Registers.SYS_MASK.Write (SYS_MASK_Reg);

         Detect_Frame_Timeout := False;
         Detect_SFD_Timeout   := False;
         Detect_PHR_Error     := False;
         Detect_RS_Error      := False;
         Detect_FCS_Error     := False;

      end Initialize;



      procedure Configure (Config : in Configuration_Type)
      is
         LDE_REPC_Reg  : DW1000.Register_Types.LDE_REPC_Type;

         SFD_Timeout : DW1000.Driver.SFD_Timeout_Number;

      begin

         LDE_REPC_Reg.LDE_REPC := LDE_Replica_Coeffs (Config.Rx_Preamble_Code);

         --  110 kbps data rate has special handling
         if Config.Data_Rate = DW1000.Driver.Data_Rate_110k then
            SYS_CFG_Reg.RXM110K := 1;

            LDE_REPC_Reg.LDE_REPC := LDE_REPC_Reg.LDE_REPC / 8;

         else
            SYS_CFG_Reg.RXM110K := 0;
         end if;

         Long_Frames := Config.PHR_Mode = DW1000.Driver.Extended_Frames;
         SYS_CFG_Reg.PHR_MODE :=
           Bits_2 (DW1000.Driver.Physical_Header_Modes'Pos (Config.PHR_Mode));

         DW1000.Registers.SYS_CFG.Write (SYS_CFG_Reg);
         DW1000.Registers.LDE_REPC.Write (LDE_REPC_Reg);

         DW1000.Driver.Configure_LDE (Config.PRF);
         DW1000.Driver.Configure_PLL (Config.Channel);
         DW1000.Driver.Configure_RF (Config.Channel);

         --  Don't allow a zero SFD timeout
         SFD_Timeout := (if Config.SFD_Timeout = 0
                         then Default_SFD_Timeout
                         else Config.SFD_Timeout);

         DW1000.Driver.Configure_DRX
           (PRF                => Config.PRF,
            Data_Rate          => Config.Data_Rate,
            Tx_Preamble_Length => Config.Tx_Preamble_Length,
            PAC                => Config.Tx_PAC,
            SFD_Timeout        => SFD_Timeout,
            Nonstandard_SFD    => Config.Use_Nonstandard_SFD);

         DW1000.Driver.Configure_AGC (Config.PRF);

         --  If a non-std SFD is used then the SFD length must be programmed
         --  for the DecaWave SFD, based on the data rate.
         if Config.Use_Nonstandard_SFD then
            Configure_Nonstandard_SFD_Length (Config.Data_Rate);
         end if;

         --  Configure the channel, Rx PRF, non-std SFD, and preamble codes
         DW1000.Registers.CHAN_CTRL.Write
           (DW1000.Register_Types.CHAN_CTRL_Type'
              (TX_CHAN  => Bits_4 (Config.Channel),
               RX_CHAN  => Bits_4 (Config.Channel),
               DWSFD    => (if Config.Use_Nonstandard_SFD then 1 else 0),
               RXPRF    => (if Config.PRF = PRF_16MHz then 2#01# else 2#10#),
               TNSSFD   => (if Config.Use_Nonstandard_SFD then 1 else 0),
               RNSSFD   => (if Config.Use_Nonstandard_SFD then 1 else 0),
               TX_PCODE => Bits_5 (Config.Tx_Preamble_Code),
               RX_PCODE => Bits_5 (Config.Rx_Preamble_Code),
               Reserved => 0));

         --  Set the Tx frame control (transmit data rate, PRF, ranging bit)
         DW1000.Registers.TX_FCTRL.Write
           (DW1000.Register_Types.TX_FCTRL_Type'
              (TFLEN    => 0,
               TFLE     => 0,
               R        => 0,
               TXBR     => Bits_2 (Data_Rates'Pos (Config.Data_Rate)),
               TR       => 1,
               TXPRF    => (if Config.PRF = PRF_16MHz then 2#01# else 2#10#),
               TXPSR    =>
                 (case Config.Tx_Preamble_Length is
                     when PLEN_64 | PLEN_128 | PLEN_256 | PLEN_512 => 2#01#,
                     when PLEN_1024 | PLEN_1536 | PLEN_2048        => 2#10#,
                     when others                                   => 2#11#),
               PE       =>
                 (case Config.Tx_Preamble_Length is
                     when PLEN_64 | PLEN_1024 | PLEN_4096 => 2#00#,
                     when PLEN_128 | PLEN_1536            => 2#01#,
                     when PLEN_256 | PLEN_2048            => 2#10#,
                     when others                          => 2#11#),
               TXBOFFS  => 0,
               IFSDELAY => 0));

         --  Load the crystal trim (if requested)
         if Use_OTP_XTAL_Trim then
            DW1000.Driver.Set_XTAL_Trim (XTAL_Trim);
         end if;

         --  Load the antenna delay (if requested)
         if Use_OTP_Antenna_Delay then
            if Config.PRF = PRF_16MHz then
               DW1000.Driver.Write_Tx_Antenna_Delay (Antenna_Delay_PRF_16);
               DW1000.Driver.Write_Rx_Antenna_Delay (Antenna_Delay_PRF_16);
            else
               DW1000.Driver.Write_Tx_Antenna_Delay (Antenna_Delay_PRF_64);
               DW1000.Driver.Write_Rx_Antenna_Delay (Antenna_Delay_PRF_64);
            end if;
         end if;

      end Configure;

      procedure Configure_Errors (Frame_Timeout : in Boolean;
                                  SFD_Timeout   : in Boolean;
                                  PHR_Error     : in Boolean;
                                  RS_Error      : in Boolean;
                                  FCS_Error     : in Boolean)
      is
         SYS_MASK_Reg : DW1000.Register_Types.SYS_MASK_Type;

      begin
         --  Configure which interrupts are enabled
         DW1000.Registers.SYS_MASK.Read (SYS_MASK_Reg);
         SYS_MASK_Reg.MRXRFTO  := (if Frame_Timeout then 1 else 0);
         SYS_MASK_Reg.MRXSFDTO := (if SFD_Timeout   then 1 else 0);
         SYS_MASK_Reg.MRXPHE   := (if PHR_Error     then 1 else 0);
         SYS_MASK_Reg.MRXRFSL  := (if RS_Error      then 1 else 0);
         SYS_MASK_Reg.MRXFCE   := (if FCS_Error     then 1 else 0);
         DW1000.Registers.SYS_MASK.Write (SYS_MASK_Reg);

         Detect_Frame_Timeout := Frame_Timeout;
         Detect_SFD_Timeout   := SFD_Timeout;
         Detect_PHR_Error     := PHR_Error;
         Detect_RS_Error      := RS_Error;
         Detect_FCS_Error     := FCS_Error;
      end Configure_Errors;

      function Get_Part_ID return Bits_32
      is
      begin
         return Part_ID;
      end Get_Part_ID;

      function Get_Lot_ID  return Bits_32
      is
      begin
         return Lot_ID;
      end Get_Lot_ID;

      function PHR_Mode return DW1000.Driver.Physical_Header_Modes
      is
      begin
         if Long_Frames then
            return Extended_Frames;
         else
            return Standard_Frames;
         end if;
      end PHR_Mode;

      procedure DW1000_IRQ
      is
         SYS_STATUS_Reg : DW1000.Register_Types.SYS_STATUS_Type;

         SYS_STATUS_Clear : DW1000.Register_Types.SYS_STATUS_Type
           := (IRQS       => 0,
               CPLOCK     => 0,
               ESYNCR     => 0,
               AAT        => 0,
               TXFRB      => 0,
               TXPRS      => 0,
               TXPHS      => 0,
               TXFRS      => 0,
               RXPRD      => 0,
               RXSFDD     => 0,
               LDEDONE    => 0,
               RXPHD      => 0,
               RXPHE      => 0,
               RXDFR      => 0,
               RXFCG      => 0,
               RXFCE      => 0,
               RXRFSL     => 0,
               RXRFTO     => 0,
               LDEERR     => 0,
               RXOVRR     => 0,
               RXPTO      => 0,
               GPIOIRQ    => 0,
               SLP2INIT   => 0,
               RFPLL_LL   => 0,
               CLKPLL_LL  => 0,
               RXSFDTO    => 0,
               HPDWARN    => 0,
               TXBERR     => 0,
               AFFREJ     => 0,
               HSRBP      => 0,
               ICRBP      => 0,
               RXRSCS     => 0,
               RXPREJ     => 0,
               TXPUTE     => 0,
               Reserved_1 => 0,
               Reserved_2 => 0);

      begin
         DW1000.Registers.SYS_STATUS.Read (SYS_STATUS_Reg);

         if SYS_STATUS_Reg.RXRFTO = 1 then
            if Detect_Frame_Timeout then
               Receiver.Notify_Receive_Error (Frame_Timeout);
            end if;
            SYS_STATUS_Clear.RXRFTO := 1;
         end if;

         if SYS_STATUS_Reg.RXSFDTO = 1 then
            if Detect_SFD_Timeout then
               Receiver.Notify_Receive_Error (SFD_Timeout);
            end if;
            SYS_STATUS_Clear.RXSFDTO := 1;
         end if;

         if SYS_STATUS_Reg.RXRFSL = 1 then
            if Detect_RS_Error then
               Receiver.Notify_Receive_Error (RS_Error);
            end if;
            SYS_STATUS_Clear.RXRFSL := 1;
         end if;

         if SYS_STATUS_Reg.RXDFR = 1 then

            if SYS_STATUS_Reg.RXFCG = 1 then
               Receiver.Notify_Frame_Received;
               SYS_STATUS_Clear.RXFCG := 1;

            elsif SYS_STATUS_Reg.RXFCE = 1 then
               if Detect_FCS_Error then
                  Receiver.Notify_Receive_Error (FCS_Error);
               end if;
               SYS_STATUS_Clear.RXFCE := 1;
            end if;

            SYS_STATUS_Clear.RXDFR := 1;
         end if;

         if SYS_STATUS_Reg.TXFRS = 1 then
            --  Frame sent
            Transmitter.Notify_Tx_Complete;
            SYS_STATUS_Clear.TXFRS := 1;
         end if;

         --  Clear events that we have seen.
         DW1000.Registers.SYS_STATUS.Write (SYS_STATUS_Clear);

      end DW1000_IRQ;

   end Driver_Type;

end DecaDriver;
