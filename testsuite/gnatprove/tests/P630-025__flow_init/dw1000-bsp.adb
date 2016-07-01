-------------------------------------------------------------------------------
-- Copyright (c) 2016 Daniel King
--
-- Permission is hereby granted, free of charge, to any person obtaining a copy
-- of this software and associated documentation files (the "Software"), to
-- deal in the Software without restriction, including without limitation the
-- rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
-- sell copies of the Software, and to permit persons to whom the Software is
-- furnished to do so, subject to the following conditions:
--
-- The above copyright notice and this permission notice shall be included in
-- all copies or substantial portions of the Software.
--
-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
-- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
-- FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
-- AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
-- LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
-- FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
-- IN THE SOFTWARE.
-------------------------------------------------------------------------------

with Interfaces;  use Interfaces;
with STM32.GPIO;
with STM32.RCC;
with STM32.SPI;

package body DW1000.BSP
with SPARK_Mode => Off
is

   procedure Select_Device
   is
   begin
      STM32.GPIO.GPIOA_Periph.BSRR.BR :=
        STM32.GPIO.BSRR_BR_Field'(As_Array => True,
                                  Arr      => (4 => 1, others => 0));
   end Select_Device;

   procedure Deselect_Device
   is
   begin
      STM32.GPIO.GPIOA_Periph.BSRR.BS :=
        STM32.GPIO.BSRR_BS_Field'(As_Array => True,
                                  Arr      => (4 => 1, others => 0));
   end Deselect_Device;

   procedure Reset_DW1000
   is
   begin
      --  Configure RSTn GPIO as output
      STM32.GPIO.GPIOA_Periph.CRL.MODE0 := 2#11#; --  Output 50 MHz
      STM32.GPIO.GPIOA_Periph.CRL.CNF0  := 2#00#; --  Output push-pull

      --  Drive the RSTn line low
      STM32.GPIO.GPIOA_Periph.BSRR.BR :=
        STM32.GPIO.BSRR_BR_Field'(As_Array => True,
                                  Arr      => (1 => 1, others => 0));

      --  Put the RSTn line to hi-Z
      STM32.GPIO.GPIOA_Periph.CRL.MODE0 := 2#00#; --  Input
      STM32.GPIO.GPIOA_Periph.CRL.CNF0  := 2#01#; --  Floating input
   end Reset_DW1000;

   procedure Write_Transaction(Header : in DW1000.Types.Byte_Array;
                               Data   : in DW1000.Types.Byte_Array)
   is
      use type STM32.Bit;

   begin

      Select_Device;

      --  Send header
      for I in Header'Range loop
         STM32.SPI.SPI1_Periph.DR.DR := Unsigned_16 (Header (I) );

         loop
            exit when STM32.SPI.SPI1_Periph.SR.TXE = 1;
         end loop;
      end loop;

      --  Send data
      for I in Data'Range loop
         loop
            exit when STM32.SPI.SPI1_Periph.SR.TXE = 1;
         end loop;

         STM32.SPI.SPI1_Periph.DR.DR := Unsigned_16 (Data (I) );
      end loop;

      --  Wait for the last byte to finish transmitting.
      loop
         exit when STM32.SPI.SPI1_Periph.SR.BSY = 0;
      end loop;

      Deselect_Device;

   end Write_Transaction;

   procedure Read_Transaction(Header : in     DW1000.Types.Byte_Array;
                              Data   :    out DW1000.Types.Byte_Array)
   is
      use type STM32.Bit;

   begin
      Select_Device;

      --  Send header
      for I in Header'Range loop
         STM32.SPI.SPI1_Periph.DR.DR := Unsigned_16 (Header (I));

         loop
            exit when STM32.SPI.SPI1_Periph.SR.TXE = 1;
         end loop;
      end loop;

      loop
         exit when STM32.SPI.SPI1_Periph.SR.BSY = 0;
      end loop;

      --  Read data
      for I in Data'Range loop
         -- Send a dummy byte to begin the transfer
         STM32.SPI.SPI1_Periph.DR.DR := 16#0000#;

         loop
            exit when STM32.SPI.SPI1_Periph.SR.BSY = 0;
         end loop;

         Data (I) := Unsigned_8 (STM32.SPI.SPI1_Periph.DR.DR and 16#FF#);
      end loop;

      Deselect_Device;

   end Read_Transaction;

begin
   --  Enable peripheral clocks
   STM32.RCC.RCC_Periph.APB2ENR.SPI1EN := 1;
   STM32.RCC.RCC_Periph.APB2ENR.AFIOEN := 1;
   STM32.RCC.RCC_Periph.APB2ENR.IOPAEN := 1;

   --  Configure GPIO
   STM32.GPIO.GPIOA_Periph.CRL.MODE4 := 2#11#;
   STM32.GPIO.GPIOA_Periph.CRL.MODE5 := 2#11#;
   STM32.GPIO.GPIOA_Periph.CRL.MODE6 := 2#00#;
   STM32.GPIO.GPIOA_Periph.CRL.MODE7 := 2#11#;
   STM32.GPIO.GPIOA_Periph.CRL.CNF4  := 2#00#;
   STM32.GPIO.GPIOA_Periph.CRL.CNF5  := 2#10#;
   STM32.GPIO.GPIOA_Periph.CRL.CNF6  := 2#10#;
   STM32.GPIO.GPIOA_Periph.CRL.CNF7  := 2#10#;

   Deselect_Device;

   Reset_DW1000;

   --  Configure SPI
   STM32.SPI.SPI1_Periph.CR1 :=
     STM32.SPI.CR1_Register'(CPHA           => 0,
                             CPOL           => 0,
                             MSTR           => 1,
                             BR             => 2#011#, --  /32 prescaler
                             SPE            => 0,
                             LSBFIRST       => 0, --  MSB first
                             SSI            => 1,
                             SSM            => 1,
                             RXONLY         => 0, --  Full duplex
                             DFF            => 0, --  8-bit data
                             CRCNEXT        => 0,
                             CRCEN          => 0, --  No CRC
                             BIDIOE         => 0,
                             BIDIMODE       => 0, --  Bidirectional
                             Reserved_16_31 => 0);
   STM32.SPI.SPI1_Periph.CRCPR.CRCPOLY := 7;
   STM32.SPI.SPI1_Periph.CR1.SPE := 1;

end DW1000.BSP;
