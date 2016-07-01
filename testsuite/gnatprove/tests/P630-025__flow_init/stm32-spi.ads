--  This spec has been automatically generated from STM32F105xx.svd

pragma Restrictions (No_Elaboration_Code);
pragma Ada_2012;

with System;

package STM32.SPI is
   pragma Preelaborate;

   ---------------
   -- Registers --
   ---------------

   ------------------
   -- CR1_Register --
   ------------------

   subtype CR1_CPHA_Field is STM32.Bit;
   subtype CR1_CPOL_Field is STM32.Bit;
   subtype CR1_MSTR_Field is STM32.Bit;
   subtype CR1_BR_Field is STM32.UInt3;
   subtype CR1_SPE_Field is STM32.Bit;
   subtype CR1_LSBFIRST_Field is STM32.Bit;
   subtype CR1_SSI_Field is STM32.Bit;
   subtype CR1_SSM_Field is STM32.Bit;
   subtype CR1_RXONLY_Field is STM32.Bit;
   subtype CR1_DFF_Field is STM32.Bit;
   subtype CR1_CRCNEXT_Field is STM32.Bit;
   subtype CR1_CRCEN_Field is STM32.Bit;
   subtype CR1_BIDIOE_Field is STM32.Bit;
   subtype CR1_BIDIMODE_Field is STM32.Bit;

   --  control register 1
   type CR1_Register is record
      --  Clock phase
      CPHA           : CR1_CPHA_Field := 16#0#;
      --  Clock polarity
      CPOL           : CR1_CPOL_Field := 16#0#;
      --  Master selection
      MSTR           : CR1_MSTR_Field := 16#0#;
      --  Baud rate control
      BR             : CR1_BR_Field := 16#0#;
      --  SPI enable
      SPE            : CR1_SPE_Field := 16#0#;
      --  Frame format
      LSBFIRST       : CR1_LSBFIRST_Field := 16#0#;
      --  Internal slave select
      SSI            : CR1_SSI_Field := 16#0#;
      --  Software slave management
      SSM            : CR1_SSM_Field := 16#0#;
      --  Receive only
      RXONLY         : CR1_RXONLY_Field := 16#0#;
      --  Data frame format
      DFF            : CR1_DFF_Field := 16#0#;
      --  CRC transfer next
      CRCNEXT        : CR1_CRCNEXT_Field := 16#0#;
      --  Hardware CRC calculation enable
      CRCEN          : CR1_CRCEN_Field := 16#0#;
      --  Output enable in bidirectional mode
      BIDIOE         : CR1_BIDIOE_Field := 16#0#;
      --  Bidirectional data mode enable
      BIDIMODE       : CR1_BIDIMODE_Field := 16#0#;
      --  unspecified
      Reserved_16_31 : STM32.Short := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CR1_Register use record
      CPHA           at 0 range 0 .. 0;
      CPOL           at 0 range 1 .. 1;
      MSTR           at 0 range 2 .. 2;
      BR             at 0 range 3 .. 5;
      SPE            at 0 range 6 .. 6;
      LSBFIRST       at 0 range 7 .. 7;
      SSI            at 0 range 8 .. 8;
      SSM            at 0 range 9 .. 9;
      RXONLY         at 0 range 10 .. 10;
      DFF            at 0 range 11 .. 11;
      CRCNEXT        at 0 range 12 .. 12;
      CRCEN          at 0 range 13 .. 13;
      BIDIOE         at 0 range 14 .. 14;
      BIDIMODE       at 0 range 15 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   ------------------
   -- CR2_Register --
   ------------------

   subtype CR2_RXDMAEN_Field is STM32.Bit;
   subtype CR2_TXDMAEN_Field is STM32.Bit;
   subtype CR2_SSOE_Field is STM32.Bit;
   subtype CR2_ERRIE_Field is STM32.Bit;
   subtype CR2_RXNEIE_Field is STM32.Bit;
   subtype CR2_TXEIE_Field is STM32.Bit;

   --  control register 2
   type CR2_Register is record
      --  Rx buffer DMA enable
      RXDMAEN       : CR2_RXDMAEN_Field := 16#0#;
      --  Tx buffer DMA enable
      TXDMAEN       : CR2_TXDMAEN_Field := 16#0#;
      --  SS output enable
      SSOE          : CR2_SSOE_Field := 16#0#;
      --  unspecified
      Reserved_3_4  : STM32.UInt2 := 16#0#;
      --  Error interrupt enable
      ERRIE         : CR2_ERRIE_Field := 16#0#;
      --  RX buffer not empty interrupt enable
      RXNEIE        : CR2_RXNEIE_Field := 16#0#;
      --  Tx buffer empty interrupt enable
      TXEIE         : CR2_TXEIE_Field := 16#0#;
      --  unspecified
      Reserved_8_31 : STM32.UInt24 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CR2_Register use record
      RXDMAEN       at 0 range 0 .. 0;
      TXDMAEN       at 0 range 1 .. 1;
      SSOE          at 0 range 2 .. 2;
      Reserved_3_4  at 0 range 3 .. 4;
      ERRIE         at 0 range 5 .. 5;
      RXNEIE        at 0 range 6 .. 6;
      TXEIE         at 0 range 7 .. 7;
      Reserved_8_31 at 0 range 8 .. 31;
   end record;

   -----------------
   -- SR_Register --
   -----------------

   subtype SR_RXNE_Field is STM32.Bit;
   subtype SR_TXE_Field is STM32.Bit;
   subtype SR_CHSIDE_Field is STM32.Bit;
   subtype SR_UDR_Field is STM32.Bit;
   subtype SR_CRCERR_Field is STM32.Bit;
   subtype SR_MODF_Field is STM32.Bit;
   subtype SR_OVR_Field is STM32.Bit;
   subtype SR_BSY_Field is STM32.Bit;

   --  status register
   type SR_Register is record
      --  Read-only. Receive buffer not empty
      RXNE          : SR_RXNE_Field := 16#0#;
      --  Read-only. Transmit buffer empty
      TXE           : SR_TXE_Field := 16#1#;
      --  Read-only. Channel side
      CHSIDE        : SR_CHSIDE_Field := 16#0#;
      --  Read-only. Underrun flag
      UDR           : SR_UDR_Field := 16#0#;
      --  CRC error flag
      CRCERR        : SR_CRCERR_Field := 16#0#;
      --  Read-only. Mode fault
      MODF          : SR_MODF_Field := 16#0#;
      --  Read-only. Overrun flag
      OVR           : SR_OVR_Field := 16#0#;
      --  Read-only. Busy flag
      BSY           : SR_BSY_Field := 16#0#;
      --  unspecified
      Reserved_8_31 : STM32.UInt24 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for SR_Register use record
      RXNE          at 0 range 0 .. 0;
      TXE           at 0 range 1 .. 1;
      CHSIDE        at 0 range 2 .. 2;
      UDR           at 0 range 3 .. 3;
      CRCERR        at 0 range 4 .. 4;
      MODF          at 0 range 5 .. 5;
      OVR           at 0 range 6 .. 6;
      BSY           at 0 range 7 .. 7;
      Reserved_8_31 at 0 range 8 .. 31;
   end record;

   -----------------
   -- DR_Register --
   -----------------

   subtype DR_DR_Field is STM32.Short;

   --  data register
   type DR_Register is record
      --  Data register
      DR             : DR_DR_Field := 16#0#;
      --  unspecified
      Reserved_16_31 : STM32.Short := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for DR_Register use record
      DR             at 0 range 0 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   --------------------
   -- CRCPR_Register --
   --------------------

   subtype CRCPR_CRCPOLY_Field is STM32.Short;

   --  CRC polynomial register
   type CRCPR_Register is record
      --  CRC polynomial register
      CRCPOLY        : CRCPR_CRCPOLY_Field := 16#7#;
      --  unspecified
      Reserved_16_31 : STM32.Short := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CRCPR_Register use record
      CRCPOLY        at 0 range 0 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   ---------------------
   -- RXCRCR_Register --
   ---------------------

   subtype RXCRCR_RxCRC_Field is STM32.Short;

   --  RX CRC register
   type RXCRCR_Register is record
      --  Read-only. Rx CRC register
      RxCRC          : RXCRCR_RxCRC_Field;
      --  unspecified
      Reserved_16_31 : STM32.Short;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for RXCRCR_Register use record
      RxCRC          at 0 range 0 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   ---------------------
   -- TXCRCR_Register --
   ---------------------

   subtype TXCRCR_TxCRC_Field is STM32.Short;

   --  TX CRC register
   type TXCRCR_Register is record
      --  Read-only. Tx CRC register
      TxCRC          : TXCRCR_TxCRC_Field;
      --  unspecified
      Reserved_16_31 : STM32.Short;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for TXCRCR_Register use record
      TxCRC          at 0 range 0 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   ----------------------
   -- I2SCFGR_Register --
   ----------------------

   subtype I2SCFGR_CHLEN_Field is STM32.Bit;
   subtype I2SCFGR_DATLEN_Field is STM32.UInt2;
   subtype I2SCFGR_CKPOL_Field is STM32.Bit;
   subtype I2SCFGR_I2SSTD_Field is STM32.UInt2;
   subtype I2SCFGR_PCMSYNC_Field is STM32.Bit;
   subtype I2SCFGR_I2SCFG_Field is STM32.UInt2;
   subtype I2SCFGR_I2SE_Field is STM32.Bit;
   subtype I2SCFGR_I2SMOD_Field is STM32.Bit;

   --  I2S configuration register
   type I2SCFGR_Register is record
      --  Channel length (number of bits per audio channel)
      CHLEN          : I2SCFGR_CHLEN_Field := 16#0#;
      --  Data length to be transferred
      DATLEN         : I2SCFGR_DATLEN_Field := 16#0#;
      --  Steady state clock polarity
      CKPOL          : I2SCFGR_CKPOL_Field := 16#0#;
      --  I2S standard selection
      I2SSTD         : I2SCFGR_I2SSTD_Field := 16#0#;
      --  unspecified
      Reserved_6_6   : STM32.Bit := 16#0#;
      --  PCM frame synchronization
      PCMSYNC        : I2SCFGR_PCMSYNC_Field := 16#0#;
      --  I2S configuration mode
      I2SCFG         : I2SCFGR_I2SCFG_Field := 16#0#;
      --  I2S Enable
      I2SE           : I2SCFGR_I2SE_Field := 16#0#;
      --  I2S mode selection
      I2SMOD         : I2SCFGR_I2SMOD_Field := 16#0#;
      --  unspecified
      Reserved_12_31 : STM32.UInt20 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for I2SCFGR_Register use record
      CHLEN          at 0 range 0 .. 0;
      DATLEN         at 0 range 1 .. 2;
      CKPOL          at 0 range 3 .. 3;
      I2SSTD         at 0 range 4 .. 5;
      Reserved_6_6   at 0 range 6 .. 6;
      PCMSYNC        at 0 range 7 .. 7;
      I2SCFG         at 0 range 8 .. 9;
      I2SE           at 0 range 10 .. 10;
      I2SMOD         at 0 range 11 .. 11;
      Reserved_12_31 at 0 range 12 .. 31;
   end record;

   --------------------
   -- I2SPR_Register --
   --------------------

   subtype I2SPR_I2SDIV_Field is STM32.Byte;
   subtype I2SPR_ODD_Field is STM32.Bit;
   subtype I2SPR_MCKOE_Field is STM32.Bit;

   --  I2S prescaler register
   type I2SPR_Register is record
      --  I2S Linear prescaler
      I2SDIV         : I2SPR_I2SDIV_Field := 16#A#;
      --  Odd factor for the prescaler
      ODD            : I2SPR_ODD_Field := 16#0#;
      --  Master clock output enable
      MCKOE          : I2SPR_MCKOE_Field := 16#0#;
      --  unspecified
      Reserved_10_31 : STM32.UInt22 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for I2SPR_Register use record
      I2SDIV         at 0 range 0 .. 7;
      ODD            at 0 range 8 .. 8;
      MCKOE          at 0 range 9 .. 9;
      Reserved_10_31 at 0 range 10 .. 31;
   end record;

   -----------------
   -- Peripherals --
   -----------------

   --  Serial peripheral interface
   type SPI_Peripheral is record
      --  control register 1
      CR1     : CR1_Register;
      --  control register 2
      CR2     : CR2_Register;
      --  status register
      SR      : SR_Register;
      --  data register
      DR      : DR_Register;
      --  CRC polynomial register
      CRCPR   : CRCPR_Register;
      --  RX CRC register
      RXCRCR  : RXCRCR_Register;
      --  TX CRC register
      TXCRCR  : TXCRCR_Register;
      --  I2S configuration register
      I2SCFGR : I2SCFGR_Register;
      --  I2S prescaler register
      I2SPR   : I2SPR_Register;
   end record
     with Volatile;

   for SPI_Peripheral use record
      CR1     at 0 range 0 .. 31;
      CR2     at 4 range 0 .. 31;
      SR      at 8 range 0 .. 31;
      DR      at 12 range 0 .. 31;
      CRCPR   at 16 range 0 .. 31;
      RXCRCR  at 20 range 0 .. 31;
      TXCRCR  at 24 range 0 .. 31;
      I2SCFGR at 28 range 0 .. 31;
      I2SPR   at 32 range 0 .. 31;
   end record;

   --  Serial peripheral interface
   SPI2_Periph : aliased SPI_Peripheral
     with Import, Address => SPI2_Base;

   --  Serial peripheral interface
   SPI3_Periph : aliased SPI_Peripheral
     with Import, Address => SPI3_Base;

   --  Serial peripheral interface
   SPI1_Periph : aliased SPI_Peripheral
     with Import, Address => SPI1_Base;

end STM32.SPI;
