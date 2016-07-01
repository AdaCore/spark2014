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

package DW1000.Constants
with SPARK_Mode => On
is

   ----------------------------------------------------------------------------
   --  OTP memory word addresses
   OTP_ADDR_EUID                : constant Bits_11 := 16#00#;
   OTP_ADDR_LDOTUNE_CAL         : constant Bits_11 := 16#04#;
   OTP_ADDR_CHIP_ID             : constant Bits_11 := 16#06#;
   OTP_ADDR_LOT_ID              : constant Bits_11 := 16#07#;
   OTP_ADDR_CH1_TX_POWER_PRF_16 : constant Bits_11 := 16#10#;
   OTP_ADDR_CH1_TX_POWER_PRF_64 : constant Bits_11 := 16#11#;
   OTP_ADDR_CH2_TX_POWER_PRF_16 : constant Bits_11 := 16#12#;
   OTP_ADDR_CH2_TX_POWER_PRF_64 : constant Bits_11 := 16#13#;
   OTP_ADDR_CH3_TX_POWER_PRF_16 : constant Bits_11 := 16#14#;
   OTP_ADDR_CH3_TX_POWER_PRF_64 : constant Bits_11 := 16#15#;
   OTP_ADDR_CH4_TX_POWER_PRF_16 : constant Bits_11 := 16#16#;
   OTP_ADDR_CH4_TX_POWER_PRF_64 : constant Bits_11 := 16#17#;
   OTP_ADDR_CH5_TX_POWER_PRF_16 : constant Bits_11 := 16#18#;
   OTP_ADDR_CH5_TX_POWER_PRF_64 : constant Bits_11 := 16#19#;
   OTP_ADDR_CH7_TX_POWER_PRF_16 : constant Bits_11 := 16#1A#;
   OTP_ADDR_CH7_TX_POWER_PRF_64 : constant Bits_11 := 16#1B#;
   OTP_ADDR_ANTENNA_DELAY       : constant Bits_11 := 16#1C#;
   OTP_ADDR_XTAL_TRIM           : constant Bits_11 := 16#E0#;

   ----------------------------------------------------------------------------
   --  Buffer lengths
   TX_BUFFER_Length             : constant := 1024;
   RX_BUFFER_Length             : constant := 1024;

end DW1000.Constants;
