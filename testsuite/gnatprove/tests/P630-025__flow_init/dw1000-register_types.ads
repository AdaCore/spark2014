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

with DW1000.Types; use DW1000.Types;
with System;

--  This package defines types for each of the DW1000 registers.
--
--  Each register type has a representation clause to match the layout of the
--  register according to the DW1000 User Manual.
package DW1000.Register_Types
with SPARK_Mode => On
is

   ----------------------------------------------------------------------------
   -- DEV_ID register file

   type DEV_ID_Type is record
      REV    : Types.Bits_4;
      VER    : Types.Bits_4;
      MODEL  : Types.Bits_8;
      RIDTAG : Types.Bits_16;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for DEV_ID_Type use record
      REV    at 0 range  0 ..  3;
      VER    at 0 range  4 ..  7;
      MODEL  at 0 range  8 .. 15;
      RIDTAG at 0 range 16 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- EUI register file

   type EUI_Type is record
      EUI : Types.Bits_64;
   end record
     with Size => 64,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EUI_Type use record
      EUI at 0 range 0 .. 63;
   end record;

   ----------------------------------------------------------------------------
   -- PANDADR register file

   type PANADR_Type is record
      SHORT_ADDR : Types.Bits_16;
      PAN_ID     : Types.Bits_16;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for PANADR_Type use record
      SHORT_ADDR at 0 range  0 .. 15;
      PAN_ID     at 0 range 16 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- SYS_CFG register file

   type SYS_CFG_Type is record
      FFEN       : Types.Bits_1;
      FFBC       : Types.Bits_1;
      FFAB       : Types.Bits_1;
      FFAD       : Types.Bits_1;
      FFAA       : Types.Bits_1;
      FFAM       : Types.Bits_1;
      FFAR       : Types.Bits_1;
      FFA4       : Types.Bits_1;
      FFA5       : Types.Bits_1;
      HIRQ_POL   : Types.Bits_1;
      SPI_EDGE   : Types.Bits_1;
      DIS_FCE    : Types.Bits_1;
      DIS_DRXB   : Types.Bits_1;
      DIS_PHE    : Types.Bits_1;
      DIS_RSDE   : Types.Bits_1;
      FCS_INT2F  : Types.Bits_1;
      PHR_MODE   : Types.Bits_2;
      DIS_STXP   : Types.Bits_1;
      RXM110K    : Types.Bits_1;
      RXWTOE     : Types.Bits_1;
      RXAUTR     : Types.Bits_1;
      AUTOACK    : Types.Bits_1;
      AACKPEND   : Types.Bits_1;

      Reserved_1 : Types.Bits_3;
      Reserved_2 : Types.Bits_5;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for SYS_CFG_Type use record
      FFEN       at 0 range  0 ..  0;
      FFBC       at 0 range  1 ..  1;
      FFAB       at 0 range  2 ..  2;
      FFAD       at 0 range  3 ..  3;
      FFAA       at 0 range  4 ..  4;
      FFAM       at 0 range  5 ..  5;
      FFAR       at 0 range  6 ..  6;
      FFA4       at 0 range  7 ..  7;
      FFA5       at 0 range  8 ..  8;
      HIRQ_POL   at 0 range  9 ..  9;
      SPI_EDGE   at 0 range 10 .. 10;
      DIS_FCE    at 0 range 11 .. 11;
      DIS_DRXB   at 0 range 12 .. 12;
      DIS_PHE    at 0 range 13 .. 13;
      DIS_RSDE   at 0 range 14 .. 14;
      FCS_INT2F  at 0 range 15 .. 15;
      PHR_MODE   at 0 range 16 .. 17;
      DIS_STXP   at 0 range 18 .. 18;

      Reserved_1 at 0 range 19 .. 21;

      RXM110K    at 0 range 22 .. 22;

      Reserved_2 at 0 range 23 .. 27;

      RXWTOE     at 0 range 28 .. 28;
      RXAUTR     at 0 range 29 .. 29;
      AUTOACK    at 0 range 30 .. 30;
      AACKPEND   at 0 range 31 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- SYS_TIME register file

   type SYS_TIME_Type is record
      SYS_TIME : Types.Bits_40;
   end record
     with Pack, Size => 40,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   ----------------------------------------------------------------------------
   -- TX_FCTRL register file

   type TX_FCTRL_Type is record
      TFLEN    : Types.Bits_7;
      TFLE     : Types.Bits_3;
      R        : Types.Bits_3;
      TXBR     : Types.Bits_2;
      TR       : Types.Bits_1;
      TXPRF    : Types.Bits_2;
      TXPSR    : Types.Bits_2;
      PE       : Types.Bits_2;
      TXBOFFS  : Types.Bits_10;
      IFSDELAY : Types.Bits_8;
   end record
     with Size => 40,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for TX_FCTRL_Type use record
      TFLEN    at 0 range  0 ..  6;
      TFLE     at 0 range  7 ..  9;
      R        at 0 range 10 .. 12;
      TXBR     at 0 range 13 .. 14;
      TR       at 0 range 15 .. 15;
      TXPRF    at 0 range 16 .. 17;
      TXPSR    at 0 range 18 .. 19;
      PE       at 0 range 20 .. 21;
      TXBOFFS  at 0 range 22 .. 31;
      IFSDELAY at 0 range 32 .. 39;
   end record;

   ----------------------------------------------------------------------------
   -- TX_BUFFER register file

   type TX_BUFFER_Type is record
      TX_BUFFER : Types.Byte_Array(1 .. 1024);
   end record
     with Size => 8192,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for TX_BUFFER_Type use record
      TX_BUFFER at 0 range 0 .. 8191;
   end record;

   ----------------------------------------------------------------------------
   -- DX_TIME register file

   type DX_TIME_Type is record
      DX_TIME : Types.Bits_40;
   end record
     with Pack, Size => 40,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   ----------------------------------------------------------------------------
   -- RX_FWTO register file

   type RX_FWTO_Type is record
      RXFWTO : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RX_FWTO_Type use record
      RXFWTO at 0 range 0 .. 15;
   end record;

   ----------------------------------------------------------------------------
   -- SYS_CTRL register file

   type SYS_CTRL_Type is record
      SFCST     : Types.Bits_1;
      TXSTRT    : Types.Bits_1;
      TXDLYS    : Types.Bits_1;
      CANSFCS   : Types.Bits_1;
      TRXOFF    : Types.Bits_1;
      WAIT4RESP : Types.Bits_1;
      RXENAB    : Types.Bits_1;
      RXDLYE    : Types.Bits_1;
      HRBPT     : Types.Bits_1;

      Reserved_1 : Types.Bits_2;
      Reserved_2 : Types.Bits_14;
      Reserved_3 : Types.Bits_7;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for SYS_CTRL_Type use record
      SFCST      at 0 range  0 ..  0;
      TXSTRT     at 0 range  1 ..  1;
      TXDLYS     at 0 range  2 ..  2;
      CANSFCS    at 0 range  3 ..  3;

      Reserved_1 at 0 range  4 ..  5;

      TRXOFF     at 0 range  6 ..  6;
      WAIT4RESP  at 0 range  7 ..  7;
      RXENAB     at 0 range  8 ..  8;
      RXDLYE     at 0 range  9 ..  9;

      Reserved_2 at 0 range 10 .. 23;

      HRBPT      at 0 range 24 .. 24;

      Reserved_3 at 0 range 25 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- SYS_MASK register file

   type SYS_MASK_Type is record
      MCPLOCK   : Types.Bits_1;
      MESYNCR   : Types.Bits_1;
      MAAT      : Types.Bits_1;
      MTXFRB    : Types.Bits_1;
      MTXPRS    : Types.Bits_1;
      MTXPHS    : Types.Bits_1;
      MTXFRS    : Types.Bits_1;
      MRXPRD    : Types.Bits_1;
      MRXSFDD   : Types.Bits_1;
      MLDEDONE  : Types.Bits_1;
      MRXPHD    : Types.Bits_1;
      MRXPHE    : Types.Bits_1;
      MRXDFR    : Types.Bits_1;
      MRXFCG    : Types.Bits_1;
      MRXFCE    : Types.Bits_1;
      MRXRFSL   : Types.Bits_1;
      MRXRFTO   : Types.Bits_1;
      MLDEERR   : Types.Bits_1;
      MRXOVRR   : Types.Bits_1;
      MRXPTO    : Types.Bits_1;
      MGPIOIRQ  : Types.Bits_1;
      MSLP2INIT : Types.Bits_1;
      MRFPLLLL  : Types.Bits_1;
      MCPLLLL   : Types.Bits_1;
      MRXSFDTO  : Types.Bits_1;
      MHPDWARN  : Types.Bits_1;
      MTXBERR   : Types.Bits_1;
      MAFFREJ   : Types.Bits_1;

      Reserved_1 : Types.Bits_1;
      Reserved_2 : Types.Bits_1;
      Reserved_3 : Types.Bits_2;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for SYS_MASK_Type use record
      Reserved_1 at 0 range 0 .. 0;

      MCPLOCK    at 0 range  1 ..  1;
      MESYNCR    at 0 range  2 ..  2;
      MAAT       at 0 range  3 ..  3;
      MTXFRB     at 0 range  4 ..  4;
      MTXPRS     at 0 range  5 ..  5;
      MTXPHS     at 0 range  6 ..  6;
      MTXFRS     at 0 range  7 ..  7;
      MRXPRD     at 0 range  8 ..  8;
      MRXSFDD    at 0 range  9 ..  9;
      MLDEDONE   at 0 range 10 .. 10;
      MRXPHD     at 0 range 11 .. 11;
      MRXPHE     at 0 range 12 .. 12;
      MRXDFR     at 0 range 13 .. 13;
      MRXFCG     at 0 range 14 .. 14;
      MRXFCE     at 0 range 15 .. 15;
      MRXRFSL    at 0 range 16 .. 16;
      MRXRFTO    at 0 range 17 .. 17;
      MLDEERR    at 0 range 18 .. 18;

      Reserved_2 at 0 range 19 .. 19;

      MRXOVRR    at 0 range 20 .. 20;
      MRXPTO     at 0 range 21 .. 21;
      MGPIOIRQ   at 0 range 22 .. 22;
      MSLP2INIT  at 0 range 23 .. 23;
      MRFPLLLL   at 0 range 24 .. 24;
      MCPLLLL    at 0 range 25 .. 25;
      MRXSFDTO   at 0 range 26 .. 26;
      MHPDWARN   at 0 range 27 .. 27;
      MTXBERR    at 0 range 28 .. 28;
      MAFFREJ    at 0 range 29 .. 29;

      Reserved_3 at 0 range 30 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- SYS_STATUS register file

   type SYS_STATUS_Type is record
      IRQS      : Types.Bits_1;
      CPLOCK    : Types.Bits_1;
      ESYNCR    : Types.Bits_1;
      AAT       : Types.Bits_1;
      TXFRB     : Types.Bits_1;
      TXPRS     : Types.Bits_1;
      TXPHS     : Types.Bits_1;
      TXFRS     : Types.Bits_1;
      RXPRD     : Types.Bits_1;
      RXSFDD    : Types.Bits_1;
      LDEDONE   : Types.Bits_1;
      RXPHD     : Types.Bits_1;
      RXPHE     : Types.Bits_1;
      RXDFR     : Types.Bits_1;
      RXFCG     : Types.Bits_1;
      RXFCE     : Types.Bits_1;
      RXRFSL    : Types.Bits_1;
      RXRFTO    : Types.Bits_1;
      LDEERR    : Types.Bits_1;
      RXOVRR    : Types.Bits_1;
      RXPTO     : Types.Bits_1;
      GPIOIRQ   : Types.Bits_1;
      SLP2INIT  : Types.Bits_1;
      RFPLL_LL  : Types.Bits_1;
      CLKPLL_LL : Types.Bits_1;
      RXSFDTO   : Types.Bits_1;
      HPDWARN   : Types.Bits_1;
      TXBERR    : Types.Bits_1;
      AFFREJ    : Types.Bits_1;
      HSRBP     : Types.Bits_1;
      ICRBP     : Types.Bits_1;
      RXRSCS    : Types.Bits_1;
      RXPREJ    : Types.Bits_1;
      TXPUTE    : Types.Bits_1;

      Reserved_1 : Types.Bits_1;
      Reserved_2 : Types.Bits_5;
   end record
     with Size => 40,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for SYS_STATUS_Type use record
      IRQS       at 0 range  0 ..  0;
      CPLOCK     at 0 range  1 ..  1;
      ESYNCR     at 0 range  2 ..  2;
      AAT        at 0 range  3 ..  3;
      TXFRB      at 0 range  4 ..  4;
      TXPRS      at 0 range  5 ..  5;
      TXPHS      at 0 range  6 ..  6;
      TXFRS      at 0 range  7 ..  7;
      RXPRD      at 0 range  8 ..  8;
      RXSFDD     at 0 range  9 ..  9;
      LDEDONE    at 0 range 10 .. 10;
      RXPHD      at 0 range 11 .. 11;
      RXPHE      at 0 range 12 .. 12;
      RXDFR      at 0 range 13 .. 13;
      RXFCG      at 0 range 14 .. 14;
      RXFCE      at 0 range 15 .. 15;
      RXRFSL     at 0 range 16 .. 16;
      RXRFTO     at 0 range 17 .. 17;
      LDEERR     at 0 range 18 .. 18;

      Reserved_1 at 0 range 19 .. 19;

      RXOVRR     at 0 range 20 .. 20;
      RXPTO      at 0 range 21 .. 21;
      GPIOIRQ    at 0 range 22 .. 22;
      SLP2INIT   at 0 range 23 .. 23;
      RFPLL_LL   at 0 range 24 .. 24;
      CLKPLL_LL  at 0 range 25 .. 25;
      RXSFDTO    at 0 range 26 .. 26;
      HPDWARN    at 0 range 27 .. 27;
      TXBERR     at 0 range 28 .. 28;
      AFFREJ     at 0 range 29 .. 29;
      HSRBP      at 0 range 30 .. 30;
      ICRBP      at 0 range 31 .. 31;
      RXRSCS     at 4 range  0 ..  0;
      RXPREJ     at 4 range  1 ..  1;
      TXPUTE     at 4 range  2 ..  2;

      Reserved_2 at 4 range  3 ..  7;
   end record;

   ----------------------------------------------------------------------------
   -- RX_FINFO register file

   type RX_FINFO_Type is record
      RXFLEN : Types.Bits_7;
      RXFLE  : Types.Bits_3;
      RXNSPL : Types.Bits_2;
      RXBR   : Types.Bits_2;
      RNG    : Types.Bits_1;
      RXPRF  : Types.Bits_2;
      RXPSR  : Types.Bits_2;
      RXPACC : Types.Bits_12;

      Reserved : Types.Bits_1;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RX_FINFO_Type use record
      RXFLEN   at 0 range  0 ..  6;
      RXFLE    at 0 range  7 ..  9;

      Reserved at 0 range 10 .. 10;

      RXNSPL   at 0 range 11 .. 12;
      RXBR     at 0 range 13 .. 14;
      RNG      at 0 range 15 .. 15;
      RXPRF    at 0 range 16 .. 17;
      RXPSR    at 0 range 18 .. 19;
      RXPACC   at 0 range 20 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- RX_BUFFER register file

   type RX_BUFFER_Type is record
      RX_BUFFER : Types.Byte_Array(1 .. 1024);
   end record
     with Size => 8192,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RX_BUFFER_Type use record
      RX_BUFFER at 0 range 0 .. 8191;
   end record;

   ----------------------------------------------------------------------------
   -- RX_FQUAL register file

   type RX_FQUAL_Type is record
      STD_NOISE : Types.Bits_16;
      FP_AMPL2  : Types.Bits_16;
      FP_AMPL3  : Types.Bits_16;
      CIR_PWR   : Types.Bits_16;
   end record
     with Size => 64,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RX_FQUAL_Type use record
      STD_NOISE at 0 range  0 .. 15;
      FP_AMPL2  at 0 range 16 .. 31;
      FP_AMPL3  at 4 range  0 .. 15;
      CIR_PWR   at 4 range 16 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- RX_TTCKI register file

   type RX_TTCKI_Type is record
      RXTTCKI : Types.Bits_32;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RX_TTCKI_Type use record
      RXTTCKI at 0 range 0 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- RX_TTCKO register file

   type RX_TTCKO_Type is record
      RXTOFS  : Types.Bits_19;
      RSMPDEL : Types.Bits_8;
      RCPHASE : Types.Bits_7;

      Reserved_1 : Types.Bits_5;
      Reserved_2 : Types.Bits_1;
   end record
     with Size => 40,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RX_TTCKO_Type use record
      RXTOFS     at 0 range  0 .. 18;

      Reserved_1 at 0 range 19 .. 23;

      RSMPDEL    at 0 range 24 .. 31;
      RCPHASE    at 4 range  0 ..  6;

      Reserved_2 at 4 range  7 ..  7;
   end record;

   ----------------------------------------------------------------------------
   -- RX_TIME register file

   type RX_TIME_Type is record
      RX_STAMP : Types.Bits_40;
      FP_INDEX : Types.Bits_16;
      FP_AMPL1 : Types.Bits_16;
      RX_RAWST : Types.Bits_40;
   end record
     with Size => 8*14,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RX_TIME_Type use record
      RX_STAMP at 0 range  0 .. 39;
      FP_INDEX at 4 range  8 .. 23;
      FP_AMPL1 at 4 range 24 .. 39;
      RX_RAWST at 8 range  8 .. 47;
   end record;

   ----------------------------------------------------------------------------
   -- TX_TIME register file

   type TX_TIME_Type is record
      TX_STAMP : Types.Bits_40;
      TX_RAWST : Types.Bits_40;
   end record
     with Size => 80,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for TX_TIME_Type use record
      TX_STAMP at 0 range 0 .. 39;
      TX_RAWST at 4 range 8 .. 47;
   end record;

   ----------------------------------------------------------------------------
   -- TX_ANTD register file

   type TX_ANTD_Type is record
      TX_ANTD : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for TX_ANTD_Type use record
      TX_ANTD at 0 range 0 .. 15;
   end record;

   ----------------------------------------------------------------------------
   -- ACK_RESP_T register file

   type ACK_RESP_T_Type is record
      W4D_TIM : Types.Bits_20;
      ACK_TIM : Types.Bits_8;

      Reserved : Types.Bits_4;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for ACK_RESP_T_Type use record
      W4D_TIM  at 0 range 0 .. 19;

      Reserved at 0 range 20 .. 23;

      ACK_TIM  at 0 range 24 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- RX_SNIFF register file

   type RX_SNIFF_Type is record
      SNIFF_ONT  : Types.Bits_4;
      SNIFF_OFFT : Types.Bits_8;

      Reserved_1 : Types.Bits_4;
      Reserved_2 : Types.Bits_16;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RX_SNIFF_Type use record
      SNIFF_ONT  at 0 range  0 ..  3;

      Reserved_1 at 0 range  4 ..  7;

      SNIFF_OFFT at 0 range  8 .. 15;

      Reserved_2 at 0 range 16 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- TX_POWER register file

   type TX_POWER_Type is record
      BOOSTNORM : Types.Bits_8;
      BOOSTP500 : Types.Bits_8;
      BOOSTP250 : Types.Bits_8;
      BOOSTP125 : Types.Bits_8;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for TX_POWER_Type use record
      BOOSTNORM at 0 range  0 ..  7;
      BOOSTP500 at 0 range  8 .. 15;
      BOOSTP250 at 0 range 16 .. 23;
      BOOSTP125 at 0 range 24 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- CHAN_CTRL register file

   type CHAN_CTRL_Type is record
      TX_CHAN  : Types.Bits_4;
      RX_CHAN  : Types.Bits_4;
      DWSFD    : Types.Bits_1;
      RXPRF    : Types.Bits_2;
      TNSSFD   : Types.Bits_1;
      RNSSFD   : Types.Bits_1;
      TX_PCODE : Types.Bits_5;
      RX_PCODE : Types.Bits_5;

      Reserved : Types.Bits_9;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for CHAN_CTRL_Type use record
      TX_CHAN  at 0 range  0 ..  3;
      RX_CHAN  at 0 range  4 ..  7;

      Reserved at 0 range  8 .. 16;

      DWSFD    at 0 range 17 .. 17;
      RXPRF    at 0 range 18 .. 19;
      TNSSFD   at 0 range 20 .. 20;
      RNSSFD   at 0 range 21 .. 21;
      TX_PCODE at 0 range 22 .. 26;
      RX_PCODE at 0 range 27 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- USR_SFD register file

   type USR_SFD_Type is record
      Sub_Registers : Types.Byte_Array(0 .. 40);
   end record
     with Size => 41*8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for USR_SFD_Type use record
      Sub_Registers at 0 range 0 .. 41*8 - 1;
   end record;

   ----------------------------------------------------------------------------
   -- AGC_CTRL register file

   -- AGC_CTRL1 sub-register
   type AGC_CTRL1_Type is record
      DIS_AM : Types.Bits_1;

      Reserved : Types.Bits_15;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AGC_CTRL1_Type use record
      DIS_AM   at 0 range 0 .. 0;

      Reserved at 0 range 1 .. 15;
   end record;

   -- AGC_TUNE1 sub-register
   type AGC_TUNE1_Type is record
      AGC_TUNE1 : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AGC_TUNE1_Type use record
      AGC_TUNE1 at 0 range 0 .. 15;
   end record;

   -- AGC_TUNE2 sub-register
   type AGC_TUNE2_Type is record
      AGC_TUNE2 : Types.Bits_32;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AGC_TUNE2_Type use record
      AGC_TUNE2 at 0 range 0 .. 31;
   end record;

   -- AGC_TUNE3 sub-register
   type AGC_TUNE3_Type is record
      AGC_TUNE3 : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AGC_TUNE3_Type use record
      AGC_TUNE3 at 0 range 0 .. 15;
   end record;

   -- AGC_STAT1 sub-register
   type AGC_STAT1_Type is record
      EDG1 : Types.Bits_5;
      EDV2 : Types.Bits_9;

      Reserved_1 : Types.Bits_6;
      Reserved_2 : Types.Bits_4;
   end record
     with Size => 24,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AGC_STAT1_Type use record
      Reserved_1 at 0 range  0 ..  5;

      EDG1       at 0 range  6 .. 10;
      EDV2       at 0 range 11 .. 19;

      Reserved_2 at 0 range 20 .. 23;
   end record;

   ----------------------------------------------------------------------------
   -- EXT_SYNC register file

   -- EC_CTRL sub-register
   type EC_CTRL_Type is record
      OSTSM  : Types.Bits_1;
      OSRSM  : Types.Bits_1;
      PLLLDT : Types.Bits_1;
      WAIT   : Types.Bits_8;
      OSTRM  : Types.Bits_1;

      Reserved : Types.Bits_20;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EC_CTRL_Type use record
      OSTSM    at 0 range  0 ..  0;
      OSRSM    at 0 range  1 ..  1;
      PLLLDT   at 0 range  2 ..  2;
      WAIT     at 0 range  3 .. 10;
      OSTRM    at 0 range 11 .. 11;

      Reserved at 0 range 12 .. 31;
   end record;

   -- EC_RXTC sub-register
   type EC_RXTC_Type is record
      RX_TS_EST : Types.Bits_32;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EC_RXTC_Type use record
      RX_TS_EST at 0 range 0 .. 31;
   end record;

   -- EC_GOLP sub-register
   type EC_GOLP_Type is record
      OFFSET_EXT : Types.Bits_6;

      Reserved   : Types.Bits_26;
   end record
   with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EC_GOLP_Type use record
      OFFSET_EXT at 0 range 0 .. 5;

      Reserved   at 0 range 6 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- ACC_MEM register file

   type ACC_MEM_Number_Type is range -32_768 .. 32_767
     with Size => 16;

   type ACC_MEM_Sample_Type is record
      Real : ACC_MEM_Number_Type;
      Imag : ACC_MEM_Number_Type;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for ACC_MEM_Sample_Type use record
      Real at 0 range 0 .. 15;
      Imag at 2 range 0 .. 15;
   end record;

   type ACC_MEM_CIR_Array is array(0 .. 1015) of ACC_MEM_Sample_Type;

   type ACC_MEM_Type is record
      CIR : ACC_MEM_CIR_Array;
   end record
     with Size => 4064*8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for ACC_MEM_Type use record
      CIR at 0 range 0 .. (4064*8) - 1;
   end record;

   ----------------------------------------------------------------------------
   -- GPIO_CTRL register file

   -- GPIO_MODE sub-register
   type GPIO_MODE_Type is record
      MSGP0 : Types.Bits_2;
      MSGP1 : Types.Bits_2;
      MSGP2 : Types.Bits_2;
      MSGP3 : Types.Bits_2;
      MSGP4 : Types.Bits_2;
      MSGP5 : Types.Bits_2;
      MSGP6 : Types.Bits_2;
      MSGP7 : Types.Bits_2;
      MSGP8 : Types.Bits_2;

      Reserved_1 : Types.Bits_6;
      Reserved_2 : Types.Bits_8;
   end record
   with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for GPIO_MODE_Type use record
      Reserved_1 at 0 range  0 ..  5;

      MSGP0      at 0 range  6 ..  7;
      MSGP1      at 0 range  8 ..  9;
      MSGP2      at 0 range 10 .. 11;
      MSGP3      at 0 range 12 .. 13;
      MSGP4      at 0 range 14 .. 15;
      MSGP5      at 0 range 16 .. 17;
      MSGP6      at 0 range 18 .. 19;
      MSGP7      at 0 range 20 .. 21;
      MSGP8      at 0 range 22 .. 23;

      Reserved_2 at 0 range 24 .. 31;
   end record;

   -- GPIO_DIR sub-register
   type GPIO_DIR_Type is record
      GDP0 : Types.Bits_1;
      GDP1 : Types.Bits_1;
      GDP2 : Types.Bits_1;
      GDP3 : Types.Bits_1;
      GDM0 : Types.Bits_1;
      GDM1 : Types.Bits_1;
      GDM2 : Types.Bits_1;
      GDM3 : Types.Bits_1;
      GDP4 : Types.Bits_1;
      GDP5 : Types.Bits_1;
      GDP6 : Types.Bits_1;
      GDP7 : Types.Bits_1;
      GDM4 : Types.Bits_1;
      GDM5 : Types.Bits_1;
      GDM6 : Types.Bits_1;
      GDM7 : Types.Bits_1;
      GDP8 : Types.Bits_1;
      GDM8 : Types.Bits_1;

      Reserved_1 : Types.Bits_3;
      Reserved_2 : Types.Bits_11;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for GPIO_DIR_Type use record
      GDP0       at 0 range  0 ..  0;
      GDP1       at 0 range  1 ..  1;
      GDP2       at 0 range  2 ..  2;
      GDP3       at 0 range  3 ..  3;
      GDM0       at 0 range  4 ..  4;
      GDM1       at 0 range  5 ..  5;
      GDM2       at 0 range  6 ..  6;
      GDM3       at 0 range  7 ..  7;
      GDP4       at 0 range  8 ..  8;
      GDP5       at 0 range  9 ..  9;
      GDP6       at 0 range 10 .. 10;
      GDP7       at 0 range 11 .. 11;
      GDM4       at 0 range 12 .. 12;
      GDM5       at 0 range 13 .. 13;
      GDM6       at 0 range 14 .. 14;
      GDM7       at 0 range 15 .. 15;
      GDP8       at 0 range 16 .. 16;

      Reserved_1 at 0 range 17 .. 19;

      GDM8       at 0 range 20 .. 20;

      Reserved_2 at 0 range 21 .. 31;
   end record;

   -- GPIO_DOUT sub-register
   type GPIO_DOUT_Type is record
      GOP0 : Types.Bits_1;
      GOP1 : Types.Bits_1;
      GOP2 : Types.Bits_1;
      GOP3 : Types.Bits_1;
      GOM0 : Types.Bits_1;
      GOM1 : Types.Bits_1;
      GOM2 : Types.Bits_1;
      GOM3 : Types.Bits_1;
      GOP4 : Types.Bits_1;
      GOP5 : Types.Bits_1;
      GOP6 : Types.Bits_1;
      GOP7 : Types.Bits_1;
      GOM4 : Types.Bits_1;
      GOM5 : Types.Bits_1;
      GOM6 : Types.Bits_1;
      GOM7 : Types.Bits_1;
      GOP8 : Types.Bits_1;
      GOM8 : Types.Bits_1;

      Reserved_1 : Types.Bits_3;
      Reserved_2 : Types.Bits_11;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for GPIO_DOUT_Type use record
      GOP0       at 0 range  0 ..  0;
      GOP1       at 0 range  1 ..  1;
      GOP2       at 0 range  2 ..  2;
      GOP3       at 0 range  3 ..  3;
      GOM0       at 0 range  4 ..  4;
      GOM1       at 0 range  5 ..  5;
      GOM2       at 0 range  6 ..  6;
      GOM3       at 0 range  7 ..  7;
      GOP4       at 0 range  8 ..  8;
      GOP5       at 0 range  9 ..  9;
      GOP6       at 0 range 10 .. 10;
      GOP7       at 0 range 11 .. 11;
      GOM4       at 0 range 12 .. 12;
      GOM5       at 0 range 13 .. 13;
      GOM6       at 0 range 14 .. 14;
      GOM7       at 0 range 15 .. 15;
      GOP8       at 0 range 16 .. 16;

      Reserved_1 at 0 range 17 .. 19;

      GOM8       at 0 range 20 .. 20;

      Reserved_2 at 0 range 21 .. 31;
   end record;

   -- GPIO_IRQE sub-register
   type GPIO_IRQE_Type is record
      GIRQE0 : Types.Bits_1;
      GIRQE1 : Types.Bits_1;
      GIRQE2 : Types.Bits_1;
      GIRQE3 : Types.Bits_1;
      GIRQE4 : Types.Bits_1;
      GIRQE5 : Types.Bits_1;
      GIRQE6 : Types.Bits_1;
      GIRQE7 : Types.Bits_1;
      GIRQE8 : Types.Bits_1;

      Reserved : Types.Bits_23;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for GPIO_IRQE_Type use record
      GIRQE0   at 0 range  0 ..  0;
      GIRQE1   at 0 range  1 ..  1;
      GIRQE2   at 0 range  2 ..  2;
      GIRQE3   at 0 range  3 ..  3;
      GIRQE4   at 0 range  4 ..  4;
      GIRQE5   at 0 range  5 ..  5;
      GIRQE6   at 0 range  6 ..  6;
      GIRQE7   at 0 range  7 ..  7;
      GIRQE8   at 0 range  8 ..  8;

      Reserved at 0 range  9 .. 31;
   end record;

   -- GPIO_ISEN sub-register
   type GPIO_ISEN_Type is record
      GISEN0 : Types.Bits_1;
      GISEN1 : Types.Bits_1;
      GISEN2 : Types.Bits_1;
      GISEN3 : Types.Bits_1;
      GISEN4 : Types.Bits_1;
      GISEN5 : Types.Bits_1;
      GISEN6 : Types.Bits_1;
      GISEN7 : Types.Bits_1;
      GISEN8 : Types.Bits_1;

      Reserved : Types.Bits_23;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for GPIO_ISEN_Type use record
      GISEN0   at 0 range  0 ..  0;
      GISEN1   at 0 range  1 ..  1;
      GISEN2   at 0 range  2 ..  2;
      GISEN3   at 0 range  3 ..  3;
      GISEN4   at 0 range  4 ..  4;
      GISEN5   at 0 range  5 ..  5;
      GISEN6   at 0 range  6 ..  6;
      GISEN7   at 0 range  7 ..  7;
      GISEN8   at 0 range  8 ..  8;

      Reserved at 0 range  9 .. 31;
   end record;

   -- GPIO_IMODE sub-register
   type GPIO_IMODE_Type is record
      GIMOD0 : Types.Bits_1;
      GIMOD1 : Types.Bits_1;
      GIMOD2 : Types.Bits_1;
      GIMOD3 : Types.Bits_1;
      GIMOD4 : Types.Bits_1;
      GIMOD5 : Types.Bits_1;
      GIMOD6 : Types.Bits_1;
      GIMOD7 : Types.Bits_1;
      GIMOD8 : Types.Bits_1;

      Reserved : Types.Bits_23;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for GPIO_IMODE_Type use record
      GIMOD0   at 0 range  0 ..  0;
      GIMOD1   at 0 range  1 ..  1;
      GIMOD2   at 0 range  2 ..  2;
      GIMOD3   at 0 range  3 ..  3;
      GIMOD4   at 0 range  4 ..  4;
      GIMOD5   at 0 range  5 ..  5;
      GIMOD6   at 0 range  6 ..  6;
      GIMOD7   at 0 range  7 ..  7;
      GIMOD8   at 0 range  8 ..  8;

      Reserved at 0 range  9 .. 31;
   end record;

   -- GPIO_IBES sub-register
   type GPIO_IBES_Type is record
      GIBES0 : Types.Bits_1;
      GIBES1 : Types.Bits_1;
      GIBES2 : Types.Bits_1;
      GIBES3 : Types.Bits_1;
      GIBES4 : Types.Bits_1;
      GIBES5 : Types.Bits_1;
      GIBES6 : Types.Bits_1;
      GIBES7 : Types.Bits_1;
      GIBES8 : Types.Bits_1;

      Reserved : Types.Bits_23;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for GPIO_IBES_Type use record
      GIBES0   at 0 range  0 ..  0;
      GIBES1   at 0 range  1 ..  1;
      GIBES2   at 0 range  2 ..  2;
      GIBES3   at 0 range  3 ..  3;
      GIBES4   at 0 range  4 ..  4;
      GIBES5   at 0 range  5 ..  5;
      GIBES6   at 0 range  6 ..  6;
      GIBES7   at 0 range  7 ..  7;
      GIBES8   at 0 range  8 ..  8;

      Reserved at 0 range  9 .. 31;
   end record;

   -- GPIO_ICLR sub-register
   type GPIO_ICLR_Type is record
      GICLR0 : Types.Bits_1;
      GICLR1 : Types.Bits_1;
      GICLR2 : Types.Bits_1;
      GICLR3 : Types.Bits_1;
      GICLR4 : Types.Bits_1;
      GICLR5 : Types.Bits_1;
      GICLR6 : Types.Bits_1;
      GICLR7 : Types.Bits_1;
      GICLR8 : Types.Bits_1;

      Reserved : Types.Bits_23;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for GPIO_ICLR_Type use record
      GICLR0   at 0 range  0 ..  0;
      GICLR1   at 0 range  1 ..  1;
      GICLR2   at 0 range  2 ..  2;
      GICLR3   at 0 range  3 ..  3;
      GICLR4   at 0 range  4 ..  4;
      GICLR5   at 0 range  5 ..  5;
      GICLR6   at 0 range  6 ..  6;
      GICLR7   at 0 range  7 ..  7;
      GICLR8   at 0 range  8 ..  8;

      Reserved at 0 range  9 .. 31;
   end record;

   -- GPIO_IDBE sub-register
   type GPIO_IDBE_Type is record
      GIDBE0 : Types.Bits_1;
      GIDBE1 : Types.Bits_1;
      GIDBE2 : Types.Bits_1;
      GIDBE3 : Types.Bits_1;
      GIDBE4 : Types.Bits_1;
      GIDBE5 : Types.Bits_1;
      GIDBE6 : Types.Bits_1;
      GIDBE7 : Types.Bits_1;
      GIDBE8 : Types.Bits_1;

      Reserved : Types.Bits_23;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for GPIO_IDBE_Type use record
      GIDBE0   at 0 range  0 ..  0;
      GIDBE1   at 0 range  1 ..  1;
      GIDBE2   at 0 range  2 ..  2;
      GIDBE3   at 0 range  3 ..  3;
      GIDBE4   at 0 range  4 ..  4;
      GIDBE5   at 0 range  5 ..  5;
      GIDBE6   at 0 range  6 ..  6;
      GIDBE7   at 0 range  7 ..  7;
      GIDBE8   at 0 range  8 ..  8;

      Reserved at 0 range  9 .. 31;
   end record;

   -- GPIO_RAW sub-register
   type GPIO_RAW_Type is record
      GRAWP0 : Types.Bits_1;
      GRAWP1 : Types.Bits_1;
      GRAWP2 : Types.Bits_1;
      GRAWP3 : Types.Bits_1;
      GRAWP4 : Types.Bits_1;
      GRAWP5 : Types.Bits_1;
      GRAWP6 : Types.Bits_1;
      GRAWP7 : Types.Bits_1;
      GRAWP8 : Types.Bits_1;

      Reserved : Types.Bits_23;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for GPIO_RAW_Type use record
      GRAWP0   at 0 range  0 ..  0;
      GRAWP1   at 0 range  1 ..  1;
      GRAWP2   at 0 range  2 ..  2;
      GRAWP3   at 0 range  3 ..  3;
      GRAWP4   at 0 range  4 ..  4;
      GRAWP5   at 0 range  5 ..  5;
      GRAWP6   at 0 range  6 ..  6;
      GRAWP7   at 0 range  7 ..  7;
      GRAWP8   at 0 range  8 ..  8;

      Reserved at 0 range  9 .. 31;
   end record;

   ----------------------------------------------------------------------------
   -- DRX_CONF register file

   -- DRX_TUNE0b sub-register
   type DRX_TUNE0b_Type is record
      DRX_TUNE0b : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for DRX_TUNE0b_Type use record
      DRX_TUNE0b at 0 range 0 .. 15;
   end record;

   -- DRX_TUNE1a sub-register
   type DRX_TUNE1a_Type is record
      DRX_TUNE1a : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for DRX_TUNE1a_Type use record
      DRX_TUNE1a at 0 range 0 .. 15;
   end record;

   -- DRX_TUNE1b sub-register
   type DRX_TUNE1b_Type is record
      DRX_TUNE1b : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for DRX_TUNE1b_Type use record
      DRX_TUNE1b at 0 range 0 .. 15;
   end record;

   -- DRX_TUNE2 sub-register
   type DRX_TUNE2_Type is record
      DRX_TUNE2 : Types.Bits_32;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for DRX_TUNE2_Type use record
      DRX_TUNE2 at 0 range 0 .. 31;
   end record;

   -- DRX_SFDTOC sub-register
   type DRX_SFDTOC_Type is record
      DRX_SFDTOC : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for DRX_SFDTOC_Type use record
      DRX_SFDTOC at 0 range 0 .. 15;
   end record;

   -- DRX_PRETOC sub-register
   type DRX_PRETOC_Type is record
      DRX_PRETOC : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for DRX_PRETOC_Type use record
      DRX_PRETOC at 0 range 0 .. 15;
   end record;

   -- DRX_TUNE4H sub-register
   type DRX_TUNE4H_Type is record
      DRX_TUNE4H : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for DRX_TUNE4H_Type use record
      DRX_TUNE4H at 0 range 0 .. 15;
   end record;

   -- RXPACC_NOSAT sub-register
   type RXPACC_NOSAT_Type is record
      RXPACC_NOSAT : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RXPACC_NOSAT_Type use record
      RXPACC_NOSAT at 0 range 0 .. 15;
   end record;

   ----------------------------------------------------------------------------
   -- RF_CONF register file

   -- RF_CONF sub-register
   type RF_CONF_Type is record
      TXFEN  : Types.Bits_5;
      PLLFEN : Types.Bits_3;
      LDOFEN : Types.Bits_5;
      TXRXSW : Types.Bits_2;

      Reserved_1 : Types.Bits_8;
      Reserved_2 : Types.Bits_9;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RF_CONF_Type use record
      Reserved_1 at 0 range  0 ..  7;

      TXFEN      at 0 range  8 .. 12;
      PLLFEN     at 0 range 13 .. 15;
      LDOFEN     at 0 range 16 .. 20;
      TXRXSW     at 0 range 21 .. 22;

      Reserved_2 at 0 range 23 .. 31;
   end record;

   -- RF_RXCTRLH sub-register
   type RF_RXCTRLH_Type is record
      RF_RXCTRLH : Types.Bits_8;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RF_RXCTRLH_Type use record
      RF_RXCTRLH at 0 range 0 .. 7;
   end record;

   -- RF_TXCTRL sub-register
   type RF_TXCTRL_Type is record
      RF_TXCTRL : Types.Bits_32;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RF_TXCTRL_Type use record
      RF_TXCTRL at 0 range 0 .. 31;
   end record;

   -- RF_STATUS sub-register
   type RF_STATUS_Type is record
      CPLLLOCK  : Types.Bits_1;
      CPLLLOW   : Types.Bits_1;
      CPLLHIGH  : Types.Bits_1;
      RFPLLLOCK : Types.Bits_1;

      Reserved  : Types.Bits_28;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for RF_STATUS_Type use record
      CPLLLOCK  at 0 range 0 .. 0;
      CPLLLOW   at 0 range 1 .. 1;
      CPLLHIGH  at 0 range 2 .. 2;
      RFPLLLOCK at 0 range 3 .. 3;

      Reserved  at 0 range 4 .. 31;
   end record;

   -- LDOTUNE sub-register
   type LDOTUNE_Type is Record
      LDOTUNE : Types.Bits_40;
   end record
     with Size => 40,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for LDOTUNE_Type use record
      LDOTUNE at 0 range 0 .. 39;
   end record;

   ----------------------------------------------------------------------------
   -- TX_CAL register file

   -- TC_SARC sub-register
   type TC_SARC_Type is record
      SAR_CTRL : Types.Bits_1;

      Reserved : Types.Bits_15;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for TC_SARC_Type use record
      SAR_CTRL at 0 range 0 .. 0;

      Reserved at 0 range 1 .. 15;
   end record;

   -- TC_SARL sub-register
   type TC_SARL_Type is record
      SAR_LVBAT : Types.Bits_8;
      SAR_LTEMP : Types.Bits_8;

      Reserved  : Types.Bits_8;
   end record
     with Size => 24,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for TC_SARL_Type use record
      SAR_LVBAT at 0 range  0 ..  7;
      SAR_LTEMP at 0 range  8 .. 15;

      Reserved  at 0 range 16 .. 23;
   end record;

   -- TC_SARW sub-register
   type TC_SARW_Type is record
      SAR_WVBAT : Types.Bits_8;
      SAR_WTEMP : Types.Bits_8;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for TC_SARW_Type use record
      SAR_WVBAT at 0 range 0 ..  7;
      SAR_WTEMP at 0 range 8 .. 15;
   end record;

   -- TC_PGDELAY sub-register
   type TC_PGDELAY_Type is record
      TC_PGDELAY : Types.Bits_8;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for TC_PGDELAY_Type use record
      TC_PGDELAY at 0 range 0 .. 7;
   end record;

   -- TC_PGTEST sub-register
   type TC_PGTEST_Type is record
      TC_PGTEST : Types.Bits_8;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for TC_PGTEST_Type use record
      TC_PGTEST at 0 range 0 .. 7;
   end record;

   ----------------------------------------------------------------------------
   -- FS_CTRL register file

   -- FS_PLLCFG sub-register
   type FS_PLLCFG_Type is record
      FS_PLLCFG : Types.Bits_32;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for FS_PLLCFG_Type use record
      FS_PLLCFG at 0 range 0 .. 31;
   end record;

   -- FS_PLLTUNE sub-register
   type FS_PLLTUNE_Type is record
      FS_PLLTUNE : Types.Bits_8;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for FS_PLLTUNE_Type use record
      FS_PLLTUNE at 0 range 0 .. 7;
   end record;

   -- FS_XTALT sub-register
   type FS_XTALT_Type is record
      XTALT    : Types.Bits_5;

      Reserved : Types.Bits_3;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for FS_XTALT_Type use record
      XTALT    at 0 range 0 .. 4;

      Reserved at 0 range 5 .. 7;
   end record;

   ----------------------------------------------------------------------------
   -- AON register file

   -- AON_WCFG sub-register
   type AON_WCFG_Type is record
      ONW_RAD    : Types.Bits_1;
      ONW_RX     : Types.Bits_1;
      ONW_LEUI   : Types.Bits_1;
      ONW_LDC    : Types.Bits_1;
      ONW_L64    : Types.Bits_1;
      PRES_SLEE  : Types.Bits_1;
      ONW_LLDE   : Types.Bits_1;
      ONW_LLD    : Types.Bits_1;

      Reserved_1 : Types.Bits_1;
      Reserved_2 : Types.Bits_2;
      Reserved_3 : Types.Bits_2;
      Reserved_4 : Types.Bits_3;
   end Record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AON_WCFG_Type use record
      ONW_RAD    at 0 range  0 ..  0;
      ONW_RX     at 0 range  1 ..  1;

      Reserved_1 at 0 range  2 .. 2;

      ONW_LEUI   at 0 range  3 ..  3;

      Reserved_2 at 0 range  4 ..  5;

      ONW_LDC    at 0 range  6 ..  6;
      ONW_L64    at 0 range  7 ..  7;
      PRES_SLEE  at 0 range  8 ..  8;

      Reserved_3 at 0 range  9 .. 10;

      ONW_LLDE   at 0 range 11 .. 11;
      ONW_LLD    at 0 range 12 .. 12;

      Reserved_4 at 0 range 13 .. 15;
   end record;

   -- AON_CTRL sub-register
   type AON_CTRL_Type is record
      RESTORE  : Types.Bits_1;
      SAVE     : Types.Bits_1;
      UPL_CFG  : Types.Bits_1;
      DCA_READ : Types.Bits_1;
      DCA_ENAB : Types.Bits_1;

      Reserved : Types.Bits_3;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AON_CTRL_Type use record
      RESTORE  at 0 range 0 .. 0;
      SAVE     at 0 range 1 .. 1;
      UPL_CFG  at 0 range 2 .. 2;
      DCA_READ at 0 range 3 .. 3;

      Reserved at 0 range 4 .. 6;

      DCA_ENAB at 0 range 7 .. 7;
   end record;

   -- AON_RDAT sub-register
   type AON_RDAT_Type is record
      AON_RDAT : Types.Bits_8;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AON_RDAT_Type use record
      AON_RDAT at 0 range 0 .. 7;
   end record;

   -- AON_ADDR sub-register
   type AON_ADDR_Type is record
      AON_ADDR : Types.Bits_8;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AON_ADDR_Type use record
      AON_ADDR at 0 range 0 .. 7;
   end record;

   -- AON_CFG0 sub-register
   type AON_CFG0_Type is record
      SLEEP_EN  : Types.Bits_1;
      WAKE_PIN  : Types.Bits_1;
      WAKE_SPI  : Types.Bits_1;
      WAKE_CNT  : Types.Bits_1;
      LPDIV_EN  : Types.Bits_1;
      LPCLKDIVA : Types.Bits_11;
      SLEEP_TIM : Types.Bits_16;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AON_CFG0_Type use record
      SLEEP_EN  at 0 range  0 ..  0;
      WAKE_PIN  at 0 range  1 ..  1;
      WAKE_SPI  at 0 range  2 ..  2;
      WAKE_CNT  at 0 range  3 ..  3;
      LPDIV_EN  at 0 range  4 ..  4;
      LPCLKDIVA at 0 range  5 .. 15;
      SLEEP_TIM at 0 range 16 .. 31;
   end record;

   -- AON_CFG1 sub-register
   type AON_CFG1_Type is record
      SLEEP_CE : Types.Bits_1;
      SMXX     : Types.Bits_1;
      LPOSC_C  : Types.Bits_1;

      Reserved : Types.Bits_13;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for AON_CFG1_Type use record
      SLEEP_CE at 0 range 0 ..  0;
      SMXX     at 0 range 1 ..  1;
      LPOSC_C  at 0 range 2 ..  2;

      Reserved at 0 range 3 .. 15;
   end record;

   ----------------------------------------------------------------------------
   -- OTP_IF register file

   -- OTP_WDAT sub-register
   type OTP_WDAT_Type is record
      OTP_WDAT : Types.Bits_32;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for OTP_WDAT_Type use record
      OTP_WDAT at 0 range 0 .. 31;
   end record;

   -- OTP_ADDR sub-register
   type OTP_ADDR_Type is record
      OTP_ADDR : Types.Bits_11;

      Reserved : Types.Bits_5;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for OTP_ADDR_Type use record
      OTP_ADDR at 0 range 0 .. 10;

      Reserved at 0 range 11 .. 15;
   end record;

   -- OTP_CTRL sub-register
   type OTP_CTRL_Type is record
      OTPRDEN : Types.Bits_1;
      OTPREAD : Types.Bits_1;
      OTPMRWR : Types.Bits_1;
      OTPPROG : Types.Bits_1;
      OTPMR   : Types.Bits_4;
      LDELOAD : Types.Bits_1;

      Reserved_1 : Types.Bits_1;
      Reserved_2 : Types.Bits_2;
      Reserved_3 : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for OTP_CTRL_Type use record
      OTPRDEN    at 0 range  0 ..  0;
      OTPREAD    at 0 range  1 ..  1;

      Reserved_1 at 0 range  2 ..  2;

      OTPMRWR    at 0 range  3 ..  3;

      Reserved_2 at 0 range  4 ..  5;

      OTPPROG    at 0 range  6 ..  6;
      OTPMR      at 0 range  7 .. 10;

      Reserved_3 at 0 range 11 .. 14;

      LDELOAD    at 0 range 15 .. 15;
   end record;

   -- OTP_STAT sub-register
   type OTP_STAT_Type is record
      OTPPRGD  : Types.Bits_1;
      OTPVPOK  : Types.Bits_1;

      Reserved : Types.Bits_14;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for OTP_STAT_Type use record
      OTPPRGD  at 0 range 0 .. 0;
      OTPVPOK  at 0 range 1 .. 1;

      Reserved at 0 range 2 .. 15;
   end record;

   -- OTP_RDAT sub-register
   type OTP_RDAT_Type is record
      OTP_RDAT : Types.Bits_32;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for OTP_RDAT_Type use record
      OTP_RDAT at 0 range 0 .. 31;
   end record;

   -- OTP_SRDAT sub-register
   type OTP_SRDAT_Type is record
      OTP_SRDAT : Types.Bits_32;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for OTP_SRDAT_Type use record
      OTP_SRDAT at 0 range 0 .. 31;
   end record;

   -- OTP_SF sub-register
   type OTP_SF_Type is record
      OPS_KICK : Types.Bits_1;
      LDO_KICK : Types.Bits_1;
      OPS_SEL  : Types.Bits_1;

      Reserved_1 : Types.Bits_3;
      Reserved_2 : Types.Bits_2;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for OTP_SF_Type use record
      OPS_KICK   at 0 range 0 .. 0;
      LDO_KICK   at 0 range 1 .. 1;

      Reserved_1 at 0 range 2 .. 4;

      OPS_SEL    at 0 range 5 .. 5;

      Reserved_2 at 0 range 6 .. 7;
   end record;

   ----------------------------------------------------------------------------
   -- LDE_IF register file

   -- LDE_THRESH sub-register
   type LDE_THRESH_Type is record
      LDE_THRESH : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for LDE_THRESH_Type use record
      LDE_THRESH at 0 range 0 .. 15;
   end record;

   -- LDE_CFG1 sub-register
   type LDE_CFG1_Type is record
      NTM   : Types.Bits_5;
      PMULT : Types.Bits_3;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for LDE_CFG1_Type use record
      NTM   at 0 range 0 .. 4;
      PMULT at 0 range 5 .. 7;
   end record;

   -- LDE_PPINDX sub-register
   type LDE_PPINDX_Type is record
      LDE_PPINDX : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for LDE_PPINDX_Type use record
      LDE_PPINDX at 0 range 0 .. 15;
   end record;

   -- LDE_PPAMPL sub-register
   type LDE_PPAMPL_Type is record
      LDE_PPAMPL : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for LDE_PPAMPL_Type use record
      LDE_PPAMPL at 0 range 0 .. 15;
   end record;

   -- LDE_RXANTD sub-register
   type LDE_RXANTD_Type is record
      LDE_RXANTD : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for LDE_RXANTD_Type use record
      LDE_RXANTD at 0 range 0 .. 15;
   end record;

   -- LDE_CFG2 sub-register
   type LDE_CFG2_Type is record
      LDE_CFG2 : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for LDE_CFG2_Type use record
      LDE_CFG2 at 0 range 0 .. 15;
   end record;

   -- LDE_REPC sub-register
   type LDE_REPC_Type is record
      LDE_REPC : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for LDE_REPC_Type use record
      LDE_REPC at 0 range 0 .. 15;
   end record;

   ----------------------------------------------------------------------------
   -- DIG_DIAG register file

   -- EVC_CTRL sub-register
   type EVC_CTRL_Type is record
      EVC_EN  : Types.Bits_1;
      EVC_CLR : Types.Bits_1;

      Reserved : Types.Bits_30;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_CTRL_Type use record
      EVC_EN   at 0 range 0 .. 0;
      EVC_CLR  at 0 range 1 .. 1;

      Reserved at 0 range 2 .. 31;
   end record;

   -- EVC_PHE sub-register
   type EVC_PHE_Type is record
      EVC_PHE : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_PHE_Type use record
      EVC_PHE  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_RSE sub-register
   type EVC_RSE_Type is record
      EVC_RSE : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_RSE_Type use record
      EVC_RSE  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_FCG sub-register
   type EVC_FCG_Type is record
      EVC_FCG : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_FCG_Type use record
      EVC_FCG  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_FCE sub-register
   type EVC_FCE_Type is record
      EVC_FCE : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_FCE_Type use record
      EVC_FCE  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_FFR sub-register
   type EVC_FFR_Type is record
      EVC_FFR : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_FFR_Type use record
      EVC_FFR  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_OVR sub-register
   type EVC_OVR_Type is record
      EVC_OVR : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_OVR_Type use record
      EVC_OVR  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_STO sub-register
   type EVC_STO_Type is record
      EVC_STO : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_STO_Type use record
      EVC_STO  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_PTO sub-register
   type EVC_PTO_Type is record
      EVC_PTO : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_PTO_Type use record
      EVC_PTO  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_FWTO sub-register
   type EVC_FWTO_Type is record
      EVC_FWTO : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_FWTO_Type use record
      EVC_FWTO  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_TXFS sub-register
   type EVC_TXFS_Type is record
      EVC_TXFS : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_TXFS_Type use record
      EVC_TXFS  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_HPW sub-register
   type EVC_HPW_Type is record
      EVC_HPW : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_HPW_Type use record
      EVC_HPW  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- EVC_TPW sub-register
   type EVC_TPW_Type is record
      EVC_TPW : Types.Bits_12;

      Reserved : Types.Bits_4;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for EVC_TPW_Type use record
      EVC_TPW  at 0 range 0 .. 11;

      Reserved at 0 range 12 .. 15;
   end record;

   -- DIAG_TMC sub-register
   type DIAG_TMC_Type is record
      TX_PSTM : Types.Bits_1;

      Reserved_1 : Types.Bits_4;
      Reserved_2 : Types.Bits_11;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for DIAG_TMC_Type use record
      Reserved_1 at 0 range 0 ..  3;

      TX_PSTM    at 0 range 4 ..  4;

      Reserved_2 at 0 range 5 .. 15;
   end record;

   ----------------------------------------------------------------------------
   -- PMSC register file

   type PMSC_CTRL0_Type is record
      SYSCLKS   : Types.Bits_2;
      RXCLKS    : Types.Bits_2;
      TXCLKS    : Types.Bits_2;
      FACE      : Types.Bits_1;
      ADCCE     : Types.Bits_1;
      AMCE      : Types.Bits_1;
      GPCE      : Types.Bits_1;
      GPRN      : Types.Bits_1;
      GPDCE     : Types.Bits_1;
      GPDRN     : Types.Bits_1;
      KHZCLKEN  : Types.Bits_1;
      SOFTRESET : Types.Bits_4;

      Reserved_1 : Types.Bits_3;
      Reserved_2 : Types.Bits_4;
      Reserved_3 : Types.Bits_3;
      Reserved_4 : Types.Bits_4;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for PMSC_CTRL0_Type use record
      SYSCLKS    at 0 range  0 ..  1;
      RXCLKS     at 0 range  2 ..  3;
      TXCLKS     at 0 range  4 ..  5;
      FACE       at 0 range  6 ..  6;

      Reserved_1 at 0 range  7 ..  9;

      ADCCE      at 0 range 10 .. 10;

      Reserved_2 at 0 range 11 .. 14;

      AMCE       at 0 range 15 .. 15;
      GPCE       at 0 range 16 .. 16;
      GPRN       at 0 range 17 .. 17;
      GPDCE      at 0 range 18 .. 18;
      GPDRN      at 0 range 19 .. 19;

      Reserved_3 at 0 range 20 .. 22;

      KHZCLKEN   at 0 range 23 .. 23;

      Reserved_4 at 0 range 24 .. 27;

      SOFTRESET  at 0 range 28 .. 31;
   end record;

   -- PMSC_CTRL1 sub-register
   type PMSC_CTRL1_Type is record
      ARX2INIT  : Types.Bits_1;
      PKTSEQ    : Types.Bits_8;
      ATXSLP    : Types.Bits_1;
      ARXSLP    : Types.Bits_1;
      SNOZE     : Types.Bits_1;
      SNOZR     : Types.Bits_1;
      PLLSYN    : Types.Bits_1;
      LDERUNE   : Types.Bits_1;
      KHZCLKDIV : Types.Bits_6;

      Reserved_1 : Types.Bits_1;
      Reserved_2 : Types.Bits_1;
      Reserved_3 : Types.Bits_1;
      Reserved_4 : Types.Bits_8;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for PMSC_CTRL1_Type use record
      Reserved_1 at 0 range 0 .. 0;

      ARX2INIT   at 0 range 1 .. 1;

      Reserved_2 at 0 range 2 .. 2;

      PKTSEQ     at 0 range 3 .. 10;
      ATXSLP     at 0 range 11 .. 11;
      ARXSLP     at 0 range 12 .. 12;
      SNOZE      at 0 range 13 .. 13;
      SNOZR      at 0 range 14 .. 14;
      PLLSYN     at 0 range 15 .. 15;

      Reserved_3 at 0 range 16 .. 16;

      LDERUNE    at 0 range 17 .. 17;

      Reserved_4 at 0 range 18 .. 25;

      KHZCLKDIV  at 0 range 26 .. 31;
   end record;

   -- PMSC_SNOZT sub-register
   type PMSC_SNOZT_Type is record
      SNOZ_TIM : Types.Bits_8;
   end record
     with Size => 8,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for PMSC_SNOZT_Type use record
      SNOZ_TIM at 0 range 0 .. 7;
   end record;

   -- PMSC_TXFSEQ sub-register
   type PMSC_TXFSEQ_Type is record
      TXFINESEQ : Types.Bits_16;
   end record
     with Size => 16,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for PMSC_TXFSEQ_Type use record
      TXFINESEQ at 0 range 0 .. 15;
   end record;

   -- PMSC_LEDC sub-register
   type PMSC_LEDC_Type is record
      BLINK_TIM : Types.Bits_8;
      BLNKEN    : Types.Bits_1;
      BLNKNOW   : Types.Bits_4;

      Reserved_1 : Types.Bits_7;
      Reserved_2 : Types.Bits_12;
   end record
     with Size => 32,
     Bit_Order => System.Low_Order_First,
     Scalar_Storage_Order => System.Low_Order_First;

   for PMSC_LEDC_Type use record
      BLINK_TIM  at 0 range 0 .. 7;
      BLNKEN     at 0 range 8 .. 8;

      Reserved_1 at 0 range 9 .. 15;

      BLNKNOW    at 0 range 16 .. 19;

      Reserved_2 at 0 range 20 .. 31;
   end record;

end DW1000.Register_Types;
