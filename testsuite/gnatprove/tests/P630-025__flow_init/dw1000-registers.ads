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

with DW1000.Generic_RO_Register_Driver;
with DW1000.Generic_WO_Register_Driver;
with DW1000.Generic_RW_Register_Driver;
with DW1000.Register_Types;
with DW1000.Types;

pragma Elaborate_All(DW1000.Generic_RO_Register_Driver);
pragma Elaborate_All(DW1000.Generic_WO_Register_Driver);
pragma Elaborate_All(DW1000.Generic_RW_Register_Driver);

-- This package defines register driver instances for each of the DW1000
-- device registers to allow for typed reading and writing each register
-- (or sub-register).
--
-- Each register is typed, using the corresponding type defined in the package
-- DW1000.Register_Types. These types allow for easy manipulation for the
-- register's fields.
--
-- Below is an example of modifying the receive and transmit channels from
-- the CHAN_CTRL register (package names omitted for clarity):
--    declare
--       Reg : CHAN_CTRL_Type;
--    begin
--       CHAN_CTRL.Read(Reg);
--       Reg.RX_CHAN := 5;
--       Reg.TX_CHAN := 5;
--       CHAN_CTRL.Write(Reg);
--    end;
package DW1000.Registers
with SPARK_Mode => On
is
   ----------------------------------------------------------------------------
   -- Register IDs
   DEV_ID_Reg_ID     : constant Types.Bits_6 := 16#00#;
   EUI_Reg_ID        : constant Types.Bits_6 := 16#01#;
   PANADR_Reg_ID     : constant Types.Bits_6 := 16#03#;
   SYS_CFG_Reg_ID    : constant Types.Bits_6 := 16#04#;
   SYS_TIME_Reg_ID   : constant Types.Bits_6 := 16#06#;
   TX_FCTRL_Reg_ID   : constant Types.Bits_6 := 16#08#;
   TX_BUFFER_Reg_ID  : constant Types.Bits_6 := 16#09#;
   DX_TIME_Reg_ID    : constant Types.Bits_6 := 16#0A#;
   RX_FWTO_Reg_ID    : constant Types.Bits_6 := 16#0C#;
   SYS_CTRL_Reg_ID   : constant Types.Bits_6 := 16#0D#;
   SYS_MASK_Reg_ID   : constant Types.Bits_6 := 16#0E#;
   SYS_STATUS_Reg_ID : constant Types.Bits_6 := 16#0F#;
   RX_FINFO_Reg_ID   : constant Types.Bits_6 := 16#10#;
   RX_BUFFER_Reg_ID  : constant Types.Bits_6 := 16#11#;
   RX_FQUAL_Reg_ID   : constant Types.Bits_6 := 16#12#;
   RX_TTCKI_Reg_ID   : constant Types.Bits_6 := 16#13#;
   RX_TTCKO_Reg_ID   : constant Types.Bits_6 := 16#14#;
   RX_TIME_Reg_ID    : constant Types.Bits_6 := 16#15#;
   TX_TIME_Reg_ID    : constant Types.Bits_6 := 16#17#;
   TX_ANTD_Reg_ID    : constant Types.Bits_6 := 16#18#;
   SYS_STATE_Reg_ID  : constant Types.Bits_6 := 16#19#;
   ACK_RESP_T_Reg_ID : constant Types.Bits_6 := 16#1A#;
   RX_SNIFF_Reg_ID   : constant Types.Bits_6 := 16#1D#;
   TX_POWER_Reg_ID   : constant Types.Bits_6 := 16#1E#;
   CHAN_CTRL_Reg_ID  : constant Types.Bits_6 := 16#1F#;
   USR_SFD_Reg_ID    : constant Types.Bits_6 := 16#21#;
   AGC_CTRL_Reg_ID   : constant Types.Bits_6 := 16#23#;
   EXT_SYNC_Reg_ID   : constant Types.Bits_6 := 16#24#;
   ACC_MEM_Reg_ID    : constant Types.Bits_6 := 16#25#;
   GPIO_CTRL_Reg_ID  : constant Types.Bits_6 := 16#26#;
   DRX_CONF_Reg_ID   : constant Types.Bits_6 := 16#27#;
   RF_CONF_Reg_ID    : constant Types.Bits_6 := 16#28#;
   TX_CAL_Reg_ID     : constant Types.Bits_6 := 16#2A#;
   FS_CTRL_Reg_ID    : constant Types.Bits_6 := 16#2B#;
   AON_Reg_ID        : constant Types.Bits_6 := 16#2C#;
   OTP_IF_Reg_ID     : constant Types.Bits_6 := 16#2D#;
   LDE_CTRL_Reg_ID   : constant Types.Bits_6 := 16#2E#;
   DIG_DIAG_Reg_ID   : constant Types.Bits_6 := 16#2F#;
   PMSC_Reg_ID       : constant Types.Bits_6 := 16#36#;

   ----------------------------------------------------------------------------
   -- Sub-Register IDs

   AGC_CTRL1_Sub_Reg_ID : constant Types.Bits_15 := 16#02#;
   AGC_TUNE1_Sub_Reg_ID : constant Types.Bits_15 := 16#04#;
   AGC_TUNE2_Sub_Reg_ID : constant Types.Bits_15 := 16#0C#;
   AGC_TUNE3_Sub_Reg_ID : constant Types.Bits_15 := 16#12#;
   AGC_STAT1_Sub_Reg_ID : constant Types.Bits_15 := 16#1E#;

   EC_CTRL_Sub_Reg_ID : constant Types.Bits_15 := 16#00#;
   EC_RXTC_Sub_Reg_ID : constant Types.Bits_15 := 16#04#;
   EC_GOLP_Sub_Reg_ID : constant Types.Bits_15 := 16#08#;

   GPIO_MODE_Sub_Reg_ID  : constant Types.Bits_15 := 16#00#;
   GPIO_DIR_Sub_Reg_ID   : constant Types.Bits_15 := 16#08#;
   GPIO_DOUT_Sub_Reg_ID  : constant Types.Bits_15 := 16#0C#;
   GPIO_IRQE_Sub_Reg_ID  : constant Types.Bits_15 := 16#10#;
   GPIO_ISEN_Sub_Reg_ID  : constant Types.Bits_15 := 16#14#;
   GPIO_IMODE_Sub_Reg_ID : constant Types.Bits_15 := 16#18#;
   GPIO_IBES_Sub_Reg_ID  : constant Types.Bits_15 := 16#1C#;
   GPIO_ICLR_Sub_Reg_ID  : constant Types.Bits_15 := 16#20#;
   GPIO_IDBE_Sub_Reg_ID  : constant Types.Bits_15 := 16#24#;
   GPIO_RAW_Sub_Reg_ID   : constant Types.Bits_15 := 16#28#;

   DRX_TUNE0b_Sub_Reg_ID   : constant Types.Bits_15 := 16#02#;
   DRX_TUNE1a_Sub_Reg_ID   : constant Types.Bits_15 := 16#04#;
   DRX_TUNE1b_Sub_Reg_ID   : constant Types.Bits_15 := 16#06#;
   DRX_TUNE2_Sub_Reg_ID    : constant Types.Bits_15 := 16#08#;
   DRX_SFDTOC_Sub_Reg_ID   : constant Types.Bits_15 := 16#20#;
   DRX_PRETOC_Sub_Reg_ID   : constant Types.Bits_15 := 16#24#;
   DRX_TUNE4H_Sub_Reg_ID   : constant Types.Bits_15 := 16#26#;
   RXPACC_NOSAT_Sub_Reg_ID : constant Types.Bits_15 := 16#2C#;

   RF_CONF_Sub_Reg_ID    : constant Types.Bits_15 := 16#00#;
   RF_RXCTRLH_Sub_Reg_ID : constant Types.Bits_15 := 16#0B#;
   RF_TXCTRL_Sub_Reg_ID  : constant Types.Bits_15 := 16#0C#;
   RF_STATUS_Sub_Reg_ID  : constant Types.Bits_15 := 16#2C#;
   LDOTUNE_Sub_Reg_ID    : constant Types.Bits_15 := 16#30#;

   TC_SARC_Sub_Reg_ID    : constant Types.Bits_15 := 16#00#;
   TC_SARL_Sub_Reg_ID    : constant Types.Bits_15 := 16#03#;
   TC_SARW_Sub_Reg_ID    : constant Types.Bits_15 := 16#06#;
   TC_PGDELAY_Sub_Reg_ID : constant Types.Bits_15 := 16#0B#;
   TC_PGTEST_Sub_Reg_ID  : constant Types.Bits_15 := 16#0C#;

   FS_PLLCFG_Sub_Reg_ID  : constant Types.Bits_15 := 16#07#;
   FS_PLLTUNE_Sub_Reg_ID : constant Types.Bits_15 := 16#0B#;
   FS_XTALT_Sub_Reg_ID   : constant Types.Bits_15 := 16#0E#;

   AON_WCFG_Sub_Reg_ID : constant Types.Bits_15 := 16#00#;
   AON_CTRL_Sub_Reg_ID : constant Types.Bits_15 := 16#02#;
   AON_RDAT_Sub_Reg_ID : constant Types.Bits_15 := 16#03#;
   AON_ADDR_Sub_Reg_ID : constant Types.Bits_15 := 16#04#;
   AON_CFG0_Sub_Reg_ID : constant Types.Bits_15 := 16#06#;
   AON_CFG1_Sub_Reg_ID : constant Types.Bits_15 := 16#0A#;

   OTP_WDAT_Sub_Reg_ID  : constant Types.Bits_15 := 16#00#;
   OTP_ADDR_Sub_Reg_ID  : constant Types.Bits_15 := 16#04#;
   OTP_CTRL_Sub_Reg_ID  : constant Types.Bits_15 := 16#06#;
   OTP_STAT_Sub_Reg_ID  : constant Types.Bits_15 := 16#08#;
   OTP_RDAT_Sub_Reg_ID  : constant Types.Bits_15 := 16#0A#;
   OTP_SRDAT_Sub_Reg_ID : constant Types.Bits_15 := 16#0E#;
   OTP_SF_Sub_Reg_ID    : constant Types.Bits_15 := 16#12#;

   LDE_THRESH_Sub_Reg_ID : constant Types.Bits_15 := 16#0000#;
   LDE_CFG1_Sub_Reg_ID   : constant Types.Bits_15 := 16#0806#;
   LDE_PPINDX_Sub_Reg_ID : constant Types.Bits_15 := 16#1000#;
   LDE_PPAMPL_Sub_Reg_ID : constant Types.Bits_15 := 16#1002#;
   LDE_RXANTD_Sub_Reg_ID : constant Types.Bits_15 := 16#1804#;
   LDE_CFG2_Sub_Reg_ID   : constant Types.Bits_15 := 16#1806#;
   LDE_REPC_Sub_Reg_ID   : constant Types.Bits_15 := 16#2804#;

   EVC_CTRL_Sub_Reg_ID : constant Types.Bits_15 := 16#00#;
   EVC_PHE_Sub_Reg_ID  : constant Types.Bits_15 := 16#04#;
   EVC_RSE_Sub_Reg_ID  : constant Types.Bits_15 := 16#06#;
   EVC_FCG_Sub_Reg_ID  : constant Types.Bits_15 := 16#08#;
   EVC_FCE_Sub_Reg_ID  : constant Types.Bits_15 := 16#0A#;
   EVC_FFR_Sub_Reg_ID  : constant Types.Bits_15 := 16#0C#;
   EVC_OVR_Sub_Reg_ID  : constant Types.Bits_15 := 16#0E#;
   EVC_STO_Sub_Reg_ID  : constant Types.Bits_15 := 16#10#;
   EVC_PTO_Sub_Reg_ID  : constant Types.Bits_15 := 16#12#;
   EVC_FWTO_Sub_Reg_ID : constant Types.Bits_15 := 16#14#;
   EVC_TXFS_Sub_Reg_ID : constant Types.Bits_15 := 16#16#;
   EVC_HPW_Sub_Reg_ID  : constant Types.Bits_15 := 16#18#;
   EVC_TPW_Sub_Reg_ID  : constant Types.Bits_15 := 16#1A#;
   DIAG_TMC_Sub_Reg_ID : constant Types.Bits_15 := 16#24#;

   PMSC_CTRL0_Sub_Reg_ID  : constant Types.Bits_15 := 16#00#;
   PMSC_CTRL1_Sub_Reg_ID  : constant Types.Bits_15 := 16#04#;
   PMSC_SNOZT_Sub_Reg_ID  : constant Types.Bits_15 := 16#0C#;
   PMSC_TXFSEQ_Sub_Reg_ID : constant Types.Bits_15 := 16#26#;
   PMSC_LEDC_Sub_Reg_ID   : constant Types.Bits_15 := 16#28#;

   ----------------------------------------------------------------------------
   -- Register Definitions

   package DEV_ID is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.DEV_ID_Type,
      Register_ID   => DEV_ID_Reg_ID);

   package EUI is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.EUI_Type,
      Register_ID   => EUI_Reg_ID);

   package PANADR is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.PANADR_Type,
      Register_ID   => PANADR_Reg_ID);

   package SYS_CFG is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.SYS_CFG_Type,
      Register_ID   => SYS_CFG_Reg_ID);

   package SYS_TIME is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.SYS_TIME_Type,
      Register_ID   => SYS_TIME_Reg_ID);

   package TX_FCTRL is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.TX_FCTRL_Type,
      Register_ID   => TX_FCTRL_Reg_ID);

   package TX_BUFFER is new DW1000.Generic_WO_Register_Driver
     (Register_Type => DW1000.Register_Types.TX_BUFFER_Type,
      Register_ID   => TX_BUFFER_Reg_ID);

   package DX_TIME is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.DX_TIME_Type,
      Register_ID   => DX_TIME_Reg_ID);

   package RX_FWTO is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.RX_FWTO_Type,
      Register_ID   => RX_FWTO_Reg_ID);

   package SYS_CTRL is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.SYS_CTRL_Type,
      Register_ID   => SYS_CTRL_Reg_ID);

   package SYS_MASK is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.SYS_MASK_Type,
      Register_ID   => SYS_MASK_Reg_ID);

   package SYS_STATUS is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.SYS_STATUS_Type,
      Register_ID   => SYS_STATUS_Reg_ID);

   package RX_FINFO is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.RX_FINFO_Type,
      Register_ID   => RX_FINFO_Reg_ID);

   package RX_BUFFER is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.RX_BUFFER_Type,
      Register_ID   => RX_BUFFER_Reg_ID);

   package RX_FQUAL is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.RX_FQUAL_Type,
      Register_ID   => RX_FQUAL_Reg_ID);

   package RX_TTCKI is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.RX_TTCKI_Type,
      Register_ID   => RX_TTCKI_Reg_ID);

   package RX_TTCKO is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.RX_TTCKO_Type,
      Register_ID   => RX_TTCKO_Reg_ID);

   package RX_TIME is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.RX_TIME_Type,
      Register_ID   => RX_TIME_Reg_ID);

   package TX_TIME is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.TX_TIME_Type,
      Register_ID   => TX_TIME_Reg_ID);

   package TX_ANTD is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.TX_ANTD_Type,
      Register_ID   => TX_ANTD_Reg_ID);

   package ACK_RESP_T is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.ACK_RESP_T_Type,
      Register_ID   => ACK_RESP_T_Reg_ID);

   package RX_SNIFF is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.RX_SNIFF_Type,
      Register_ID   => RX_SNIFF_Reg_ID);

   package TX_POWER is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.TX_POWER_Type,
      Register_ID   => TX_POWER_Reg_ID);

   package CHAN_CTRL is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.CHAN_CTRL_Type,
      Register_ID   => CHAN_CTRL_Reg_ID);

   package USR_SFD is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.USR_SFD_Type,
      Register_ID   => USR_SFD_Reg_ID);

   package AGC_CTRL1 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.AGC_CTRL1_Type,
      Register_ID   => AGC_CTRL_Reg_ID,
      Sub_Register  => AGC_CTRL1_Sub_Reg_ID);

   package AGC_TUNE1 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.AGC_TUNE1_Type,
      Register_ID   => AGC_CTRL_Reg_ID,
      Sub_Register  => AGC_CTRL1_Sub_Reg_ID);

   package AGC_TUNE2 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.AGC_TUNE2_Type,
      Register_ID   => AGC_CTRL_Reg_ID,
      Sub_Register  => AGC_TUNE2_Sub_Reg_ID);

   package AGC_TUNE3 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.AGC_TUNE3_Type,
      Register_ID   => AGC_CTRL_Reg_ID,
      Sub_Register  => AGC_TUNE3_Sub_Reg_ID);

   package AGC_STAT1 is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.AGC_STAT1_Type,
      Register_ID   => AGC_CTRL_Reg_ID,
      Sub_Register  => AGC_STAT1_Sub_Reg_ID);

   package EC_CTRL is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.EC_CTRL_Type,
      Register_ID   => EXT_SYNC_Reg_ID,
      Sub_Register  => EC_CTRL_Sub_Reg_ID);

   package EC_RXTC is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EC_RXTC_Type,
      Register_ID   => EXT_SYNC_Reg_ID,
      Sub_Register  => EC_RXTC_Sub_Reg_ID);

   package EC_GOLP is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EC_GOLP_Type,
      Register_ID   => EXT_SYNC_Reg_ID,
      Sub_Register  => EC_GOLP_Sub_Reg_ID);

   package ACC_MEM is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.ACC_MEM_Type,
      Register_ID   => ACC_MEM_Reg_ID);

   package GPIO_MODE is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.GPIO_MODE_Type,
      Register_ID   => GPIO_CTRL_Reg_ID,
      Sub_Register  => GPIO_MODE_Sub_Reg_ID);

   package GPIO_DIR is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.GPIO_DIR_Type,
      Register_ID   => GPIO_CTRL_Reg_ID,
      Sub_Register  => GPIO_DIR_Sub_Reg_ID);

   package GPIO_DOUT is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.GPIO_DOUT_Type,
      Register_ID   => GPIO_CTRL_Reg_ID,
      Sub_Register  => GPIO_DOUT_Sub_Reg_ID);

   package GPIO_IRQE is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.GPIO_IRQE_Type,
      Register_ID   => GPIO_CTRL_Reg_ID,
      Sub_Register  => GPIO_IRQE_Sub_Reg_ID);

   package GPIO_ISEN is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.GPIO_ISEN_Type,
      Register_ID   => GPIO_CTRL_Reg_ID,
      Sub_Register  => GPIO_ISEN_Sub_Reg_ID);

   package GPIO_IMODE is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.GPIO_IMODE_Type,
      Register_ID   => GPIO_CTRL_Reg_ID,
      Sub_Register  => GPIO_IMODE_Sub_Reg_ID);

   package GPIO_IBES is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.GPIO_IBES_Type,
      Register_ID   => GPIO_CTRL_Reg_ID,
      Sub_Register  => GPIO_IBES_Sub_Reg_ID);

   package GPIO_ICLR is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.GPIO_ICLR_Type,
      Register_ID   => GPIO_CTRL_Reg_ID,
      Sub_Register  => GPIO_ICLR_Sub_Reg_ID);

   package GPIO_IDBE is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.GPIO_IDBE_Type,
      Register_ID   => GPIO_CTRL_Reg_ID,
      Sub_Register  => GPIO_IDBE_Sub_Reg_ID);

   package GPIO_RAW is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.GPIO_RAW_Type,
      Register_ID   => GPIO_CTRL_Reg_ID,
      Sub_Register  => GPIO_RAW_Sub_Reg_ID);

   package DRX_TUNE0b is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.DRX_TUNE0b_Type,
      Register_ID   => DRX_CONF_Reg_ID,
      Sub_Register  => DRX_TUNE0b_Sub_Reg_ID);

   package DRX_TUNE1a is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.DRX_TUNE1a_Type,
      Register_ID   => DRX_CONF_Reg_ID,
      Sub_Register  => DRX_TUNE1a_Sub_Reg_ID);

   package DRX_TUNE1b is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.DRX_TUNE1b_Type,
      Register_ID   => DRX_CONF_Reg_ID,
      Sub_Register  => DRX_TUNE1b_Sub_Reg_ID);

   package DRX_TUNE2 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.DRX_TUNE2_Type,
      Register_ID   => DRX_CONF_Reg_ID,
      Sub_Register  => DRX_TUNE2_Sub_Reg_ID);

   package DRX_SFDTOC is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.DRX_SFDTOC_Type,
      Register_ID   => DRX_CONF_Reg_ID,
      Sub_Register  => DRX_SFDTOC_Sub_Reg_ID);

   package DRX_PRETOC is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.DRX_PRETOC_Type,
      Register_ID   => DRX_CONF_Reg_ID,
      Sub_Register  => DRX_PRETOC_Sub_Reg_ID);

   package DRX_TUNE4H is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.DRX_TUNE4H_Type,
      Register_ID   => DRX_CONF_Reg_ID,
      Sub_Register  => DRX_TUNE4H_Sub_Reg_ID);

   package RXPACC_NOSAT is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.RXPACC_NOSAT_Type,
      Register_ID   => DRX_CONF_Reg_ID,
      Sub_Register  => RXPACC_NOSAT_Sub_Reg_ID);

   package RF_CONF is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.RF_CONF_Type,
      Register_ID   => RF_CONF_Reg_ID,
      Sub_Register  => RF_CONF_Sub_Reg_ID);

   package RF_RXCTRLH is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.RF_RXCTRLH_Type,
      Register_ID   => RF_CONF_Reg_ID,
      Sub_Register  => RF_RXCTRLH_Sub_Reg_ID);

   package RF_TXCTRL is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.RF_TXCTRL_Type,
      Register_ID   => RF_CONF_Reg_ID,
      Sub_Register  => RF_TXCTRL_Sub_Reg_ID);

   package RF_STATUS is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.RF_STATUS_Type,
      Register_ID   => RF_CONF_Reg_ID,
      Sub_Register  => RF_STATUS_Sub_Reg_ID);

   package LDOTUNE is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.LDOTUNE_Type,
      Register_ID   => RF_CONF_Reg_ID,
      Sub_Register  => LDOTUNE_Sub_Reg_ID);

   package TC_SARC is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.TC_SARC_Type,
      Register_ID   => TX_CAL_Reg_ID,
      Sub_Register  => TC_SARC_Sub_Reg_ID);

   package TC_SARL is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.TC_SARL_Type,
      Register_ID   => TX_CAL_Reg_ID,
      Sub_Register  => TC_SARL_Sub_Reg_ID);

   package TC_SARW is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.TC_SARW_Type,
      Register_ID   => TX_CAL_Reg_ID,
      Sub_Register  => TC_SARW_Sub_Reg_ID);

   package TC_PGDELAY is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.TC_PGDELAY_Type,
      Register_ID   => TX_CAL_Reg_ID,
      Sub_Register  => TC_PGDELAY_Sub_Reg_ID);

   package TC_PGTEST is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.TC_PGTEST_Type,
      Register_ID   => TX_CAL_Reg_ID,
      Sub_Register  => TC_PGTEST_Sub_Reg_ID);

   package FS_PLLCFG is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.FS_PLLCFG_Type,
      Register_ID   => FS_CTRL_Reg_ID,
      Sub_Register  => FS_PLLCFG_Sub_Reg_ID);

   package FS_PLLTUNE is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.FS_PLLTUNE_Type,
      Register_ID   => FS_CTRL_Reg_ID,
      Sub_Register  => FS_PLLTUNE_Sub_Reg_ID);

   package FS_XTALT is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.FS_XTALT_Type,
      Register_ID   => FS_CTRL_Reg_ID,
      Sub_Register  => FS_XTALT_Sub_Reg_ID);

   package AON_WCFG is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.AON_WCFG_Type,
      Register_ID   => AON_Reg_ID,
      Sub_Register  => AON_WCFG_Sub_Reg_ID);

   package AON_CTRL is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.AON_CTRL_Type,
      Register_ID   => AON_Reg_ID,
      Sub_Register  => AON_CTRL_Sub_Reg_ID);

   package AON_RDAT is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.AON_RDAT_Type,
      Register_ID   => AON_Reg_ID,
      Sub_Register  => AON_RDAT_Sub_Reg_ID);

   package AON_ADDR is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.AON_ADDR_Type,
      Register_ID   => AON_Reg_ID,
      Sub_Register  => AON_ADDR_Sub_Reg_ID);

   package AON_CFG0 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.AON_CFG0_Type,
      Register_ID   => AON_Reg_ID,
      Sub_Register  => AON_CFG0_Sub_Reg_ID);

   package AON_CFG1 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.AON_CFG1_Type,
      Register_ID   => AON_Reg_ID,
      Sub_Register  => AON_CFG1_Sub_Reg_ID);

   package OTP_WDAT is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.OTP_WDAT_Type,
      Register_ID   => OTP_IF_Reg_ID,
      Sub_Register  => OTP_WDAT_Sub_Reg_ID);

   package OTP_ADDR is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.OTP_ADDR_Type,
      Register_ID   => OTP_IF_Reg_ID,
      Sub_Register  => OTP_ADDR_Sub_Reg_ID);

   package OTP_CTRL is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.OTP_CTRL_Type,
      Register_ID   => OTP_IF_Reg_ID,
      Sub_Register  => OTP_CTRL_Sub_Reg_ID);

   package OTP_STAT is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.OTP_STAT_Type,
      Register_ID   => OTP_IF_Reg_ID,
      Sub_Register  => OTP_STAT_Sub_Reg_ID);

   package OTP_RDAT is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.OTP_RDAT_Type,
      Register_ID   => OTP_IF_Reg_ID,
      Sub_Register  => OTP_RDAT_Sub_Reg_ID);

   package OTP_SRDAT is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.OTP_SRDAT_Type,
      Register_ID   => OTP_IF_Reg_ID,
      Sub_Register  => OTP_SRDAT_Sub_Reg_ID);

   package OTP_SF is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.OTP_SF_Type,
      Register_ID   => OTP_IF_Reg_ID,
      Sub_Register  => OTP_SF_Sub_Reg_ID);

   package LDE_THRESH is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.LDE_THRESH_Type,
      Register_ID   => LDE_CTRL_Reg_ID,
      Sub_Register  => LDE_THRESH_Sub_Reg_ID);

   package LDE_CFG1 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.LDE_CFG1_Type,
      Register_ID   => LDE_CTRL_Reg_ID,
      Sub_Register  => LDE_CFG1_Sub_Reg_ID);

   package LDE_PPINDX is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.LDE_PPINDX_Type,
      Register_ID   => LDE_CTRL_Reg_ID,
      Sub_Register  => LDE_PPINDX_Sub_Reg_ID);

   package LDE_PPAMPL is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.LDE_PPAMPL_Type,
      Register_ID   => LDE_CTRL_Reg_ID,
      Sub_Register  => LDE_PPAMPL_Sub_Reg_ID);

   package LDE_RXANTD is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.LDE_RXANTD_Type,
      Register_ID   => LDE_CTRL_Reg_ID,
      Sub_Register  => LDE_RXANTD_Sub_Reg_ID);

   package LDE_CFG2 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.LDE_CFG2_Type,
      Register_ID   => LDE_CTRL_Reg_ID,
      Sub_Register  => LDE_CFG2_Sub_Reg_ID);

   package LDE_REPC is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.LDE_REPC_Type,
      Register_ID   => LDE_CTRL_Reg_ID,
      Sub_Register  => LDE_REPC_Sub_Reg_ID);

   package EVC_CTRL is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_CTRL_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_CTRL_Sub_Reg_ID);

   package EVC_PHE is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_PHE_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_PHE_Sub_Reg_ID);

   package EVC_RSE is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_RSE_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_RSE_Sub_Reg_ID);

   package EVC_FCG is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_FCG_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_FCG_Sub_Reg_ID);

   package EVC_FCE is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_FCE_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_FCE_Sub_Reg_ID);

   package EVC_FFR is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_FFR_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_FFR_Sub_Reg_ID);

   package EVC_OVR is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_OVR_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_OVR_Sub_Reg_ID);

   package EVC_STO is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_STO_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_STO_Sub_Reg_ID);

   package EVC_PTO is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_PTO_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_PTO_Sub_Reg_ID);

   package EVC_FWTO is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_FWTO_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_FWTO_Sub_Reg_ID);

   package EVC_TXFS is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_TXFS_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_TXFS_Sub_Reg_ID);

   package EVC_HPW is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_HPW_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_HPW_Sub_Reg_ID);

   package EVC_TPW is new DW1000.Generic_RO_Register_Driver
     (Register_Type => DW1000.Register_Types.EVC_TPW_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => EVC_TPW_Sub_Reg_ID);

   package DIAG_TMC is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.DIAG_TMC_Type,
      Register_ID   => DIG_DIAG_Reg_ID,
      Sub_Register  => DIAG_TMC_Sub_Reg_ID);

   package PMSC_CTRL0 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.PMSC_CTRL0_Type,
      Register_ID   => PMSC_Reg_ID,
      Sub_Register  => PMSC_CTRL0_Sub_Reg_ID);

   package PMSC_CTRL1 is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.PMSC_CTRL1_Type,
      Register_ID   => PMSC_Reg_ID,
      Sub_Register  => PMSC_CTRL1_Sub_Reg_ID);

   package PMSC_SNOZT is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.PMSC_SNOZT_Type,
      Register_ID   => PMSC_Reg_ID,
      Sub_Register  => PMSC_SNOZT_Sub_Reg_ID);

   package PMSC_TXFSEQ is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.PMSC_TXFSEQ_Type,
      Register_ID   => PMSC_Reg_ID,
      Sub_Register  => PMSC_TXFSEQ_Sub_Reg_ID);

   package PMSC_LEDC is new DW1000.Generic_RW_Register_Driver
     (Register_Type => DW1000.Register_Types.PMSC_LEDC_Type,
      Register_ID   => PMSC_Reg_ID,
      Sub_Register  => PMSC_LEDC_Sub_Reg_ID);


end DW1000.Registers;
