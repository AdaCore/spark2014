 --
 --  Automatically generated Ada config: don't edit
 --  Project: MOTH
 --  Version: 0.0.1
 --  Thu Feb 21 10:22:31 2019
 --

package OpenConf is
  CONFIG_ARCH_SPARC : constant Boolean := true;
  CONFIG_APP_INTERRUPT : constant Boolean := true;
  CONFIG_LIBMOTH : constant Boolean := true;
  CONFIG_ARCH : constant string := "sparc";
  CONFIG_APP_APP1 : constant Boolean := true;
  CONFIG_APP_APP2 : constant Boolean := true;
  CONFIG_APP_APP3 : constant Boolean := true;
  CONFIG_MBX_MSG_SIZE_1 : constant Boolean := false;
  CONFIG_MBX_MSG_SIZE_2 : constant Boolean := false;
  CONFIG_LEON_NONE_UART : constant Boolean := false;
  CONFIG_MBX_MSG_SIZE_4 : constant Boolean := true;
  CONFIG_ARCH_ARM : constant Boolean := false;
  CONFIG_MBX_MSG_SIZE_8 : constant Boolean := false;
  CONFIG_MAX_TASK_COUNT : constant := 5;
  CONFIG_TASK_MBX_COUNT : constant := 3;
  CONFIG_ARCH_x86 : constant Boolean := false;
  CONFIG_BOARD : constant string := "qemu";
  CONFIG_CPU_SPARC_LEON3 : constant Boolean := true;
  CONFIG_MBX_SIZE : constant := 32;
  CONFIG_CPU_SPARC_LEON4 : constant Boolean := false;
  CONFIG_GRLIB_UART_ADDR : constant := 16#80000100#;
  CONFIG_BOARD_LEON_QEMU : constant Boolean := true;
  CONFIG_BOARD_LEON_TSIM : constant Boolean := false;
  CONFIG_LEON_GRLIB_UART : constant Boolean := true;
  CONFIG_VERBOSE_MODE : constant Boolean := false;
  CONFIG_APP_TIMER : constant Boolean := true;
  CONFIG_NONE_UART : constant Boolean := false;
  CONFIG_GRLIB_IRQMP_ADDR : constant := 16#80000200#;
  CONFIG_LEON_GRLIB_IRQMP : constant Boolean := true;
  CONFIG_CPU : constant string := "leon3";
end OpenConf;
