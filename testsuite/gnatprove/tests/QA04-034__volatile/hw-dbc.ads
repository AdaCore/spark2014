--
-- Copyright (C) 2016-2017 secunet Security Networks AG
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--

with Libxhcidbg_Component.Devices;

with HW.Sub_Regs;
with HW.MMIO_Regs;
pragma Elaborate_All (HW.MMIO_Regs);
with HW.MMIO_Range;
pragma Elaborate_All (HW.MMIO_Range);

package HW.DbC
with
   Abstract_State => (State, (DMA with External))
is

   procedure Init;

   procedure Poll (Now : Boolean := False);

   procedure Receive
     (Buf : in out Buffer;
      Len : in out Natural)
   with
      Post => Len <= Len'Old;

   procedure Send
     (Buf      : in     Buffer;
      Len      : in out Natural;
      Success  :    out Boolean)
   with
      Post => Len <= Len'Old;

   ----------------------------------------------------------------------------

private

   type Word2  is mod 2 **  2;
   type Word3  is mod 2 **  3;
   type Word4  is mod 2 **  4;
   type Word5  is mod 2 **  5;
   type Word10 is mod 2 ** 10;
   type Word19 is mod 2 ** 19;
   type Word20 is mod 2 ** 20;
   type Word28 is mod 2 ** 28;

   type Error is (
      Success,
      Communication_Error,
      Driver_Error,
      Stall_Error,
      Data_Residue,
      Bad_Descriptor,
      Not_Enough_Bandwidth,
      Unsupported_Size,
      Unsupported_Count,
      No_Space_Left,
      Unknown_Device_Class,
      Invalid_Data,
      Invalid_Request,
      Timeout,
      Class_Prohibited,
      Initialization_Error,
      Controller_Error,
      No_USB2_Address,
      Device_Not_Supported,
      Unknown_Error);

   ----------------------------------------------------------------------------

   Max_DMA_Xfers : constant   := 64;
   Max_Bulk_Size : constant   := 4096;
   Highest_Address : constant := 16#0000_ffff_ffff_ffff#;

   Endpoint_Count : constant  := 3;
   -- Endpoint 1 (the control endpoint) is handled by hardware
   -- Endpoint 2 is the bulk out endpoint
   -- Endpoint 3 is the bulk in endpoint
   subtype Endpoint_Range is Positive range 2 .. Endpoint_Count;

   type Global_Transfer_Id is range 0 .. Max_DMA_Xfers - 1;
   -- DMA space for the last transfer is reserved for the kernel.
   subtype Transfer_Id is
      Global_Transfer_Id range 0 .. Global_Transfer_Id'Last - 1;

   ----------------------------------------------------------------------------

   MMIO_Size : constant := Libxhcidbg_Component.Devices.Xhci_Xhci_Registers_Size;
   type MMIO_Index is range 0 .. MMIO_Size / 4 - 1;
   type MMIO_Array is array (MMIO_Index) of Word32
   with
      Atomic_Components,
      Size => MMIO_Size * 8;
   pragma Warnings (Off, "atomic synchronization set");
   package MMIO is new MMIO_Range
     (Base_Addr   => Libxhcidbg_Component.Devices.Xhci_Xhci_Registers_Address,
      Element_T   => Word32,
      Index_T     => MMIO_Index,
      Array_T     => MMIO_Array);
   pragma Warnings (On, "atomic synchronization set");

   type Cap_Registers is
     (Capability_Registers_Length,
      XHCI_Extended_Caps);
   package Cap_S_Regs is new Sub_Regs (Cap_Registers);
   Cap_Reg_Descs : constant Cap_S_Regs.Array_T :=
     (Capability_Registers_Length      => (16#00#,  7,  0),
      XHCI_Extended_Caps               => (16#10#, 31, 16));
   package Cap_Regs is new MMIO_Regs (MMIO, 0, Cap_S_Regs, Cap_Reg_Descs);

   type Op_Registers is
     (Run_Stop,
      Host_Controller_Reset,
      HC_Halted,
      Controller_Not_Ready);
   package Op_S_Regs is new Sub_Regs (Op_Registers);
   Op_Reg_Descs : constant Op_S_Regs.Array_T :=
     (Run_Stop                         => (16#00#,  0,  0),
      Host_Controller_Reset            => (16#00#,  1,  1),
      HC_Halted                        => (16#04#,  0,  0),
      Controller_Not_Ready             => (16#04#, 11, 11));
   package Op_Regs is new MMIO_Regs (MMIO, 0, Op_S_Regs, Op_Reg_Descs);

   type xCap_Registers is
     (Capability_ID,
      Next_xCap);
   package xCap_S_Regs is new Sub_Regs (xCap_Registers);
   xCap_Reg_Descs : constant xCap_S_Regs.Array_T :=
     (Capability_ID                    => (16#00#,  7,  0),
      Next_xCap                        => (16#00#, 15,  8));
   package xCap_Regs is new MMIO_Regs (MMIO, 0, xCap_S_Regs, xCap_Reg_Descs);
   procedure Find_Next_xCap (Cap_Id : in Word8; Success : out Boolean);

   type Legacy_Support_Registers is
     (HC_BIOS_Owned_Semaphore,
      HC_OS_Owned_Semaphore);
   package Legacy_Support_S_Regs is new Sub_Regs (Legacy_Support_Registers);
   Legacy_Support_Reg_Descs : constant Legacy_Support_S_Regs.Array_T :=
     (HC_BIOS_Owned_Semaphore => (16#00#, 16, 16),
      HC_OS_Owned_Semaphore   => (16#00#, 24, 24));
   package Legacy_Support_Regs is new MMIO_Regs
     (DbC.MMIO, 0, Legacy_Support_S_Regs, Legacy_Support_Reg_Descs);

   type Registers is
     (Doorbell_Target,
      ERST_Size,
      ERST_Base_Lo,
      ERST_Base_Hi,
      ER_Dequeue_Ptr_Lo,
      ER_Dequeue_Ptr_Hi,
      DBC_CONTROL,
      DbC_Run,
      Link_Status_Event_Enable,
      Halt_OUT_TR,
      Halt_IN_TR,
      DbC_Run_Change,
      Debug_Max_Burst_Size,
      Device_Address,
      DbC_Enable,
      DBC_STATUS,
      Event_Ring_Not_Empty,
      DbC_System_Bus_Reset,
      Debug_Port_Number,
      DBC_PORTSC,
      Current_Connect_Status,
      Port_Enable_Disable,
      Port_Reset,
      Port_Link_State,
      Port_Speed,
      Connect_Status_Change,
      Port_Reset_Change,
      Port_Link_Status_Change,
      Port_Config_Error_Change,
      Context_Pointer_Lo,
      Context_Pointer_Hi,
      DbC_Protocol,
      Vendor_ID,
      Product_ID,
      Device_Revision);
   package S_Regs is new Sub_Regs (Registers);
   Reg_Descs : constant S_Regs.Array_T :=
     (Doorbell_Target                  => (16#04#, 15,  8),
      ERST_Size                        => (16#08#, 15,  0),
      ERST_Base_Lo                     => (16#10#, 31,  0),
      ERST_Base_Hi                     => (16#14#, 31,  0),
      ER_Dequeue_Ptr_Lo                => (16#18#, 31,  0),
      ER_Dequeue_Ptr_Hi                => (16#1c#, 31,  0),
      DBC_CONTROL                      => (16#20#, 31,  0),
      DbC_Run                          => (16#20#,  0,  0),
      Link_Status_Event_Enable         => (16#20#,  1,  1),
      Halt_OUT_TR                      => (16#20#,  2,  2),
      Halt_IN_TR                       => (16#20#,  3,  3),
      DbC_Run_Change                   => (16#20#,  4,  4),
      Debug_Max_Burst_Size             => (16#20#, 23, 16),
      Device_Address                   => (16#20#, 30, 24),
      DbC_Enable                       => (16#20#, 31, 31),
      DBC_STATUS                       => (16#24#, 31,  0),
      Event_Ring_Not_Empty             => (16#24#,  0,  0),
      DbC_System_Bus_Reset             => (16#24#,  1,  1),
      Debug_Port_Number                => (16#24#, 31, 24),
      DBC_PORTSC                       => (16#28#, 31,  0),
      Current_Connect_Status           => (16#28#,  0,  0),
      Port_Enable_Disable              => (16#28#,  1,  1),
      Port_Reset                       => (16#28#,  4,  4),
      Port_Link_State                  => (16#28#,  8,  5),
      Port_Speed                       => (16#28#, 13, 10),
      Connect_Status_Change            => (16#28#, 17, 17),
      Port_Reset_Change                => (16#28#, 21, 21),
      Port_Link_Status_Change          => (16#28#, 22, 22),
      Port_Config_Error_Change         => (16#28#, 23, 23),
      Context_Pointer_Lo               => (16#30#, 31,  0),
      Context_Pointer_Hi               => (16#34#, 31,  0),
      DbC_Protocol                     => (16#38#,  7,  0),
      Vendor_ID                        => (16#38#, 31, 16),
      Product_ID                       => (16#3c#, 15,  0),
      Device_Revision                  => (16#3c#, 31, 16));
   package Regs is new MMIO_Regs (MMIO, 0, S_Regs, Reg_Descs);

   procedure Ring_Doorbell (EP : Endpoint_Range)
   with
      Pre => Regs.Byte_Offset /= 0;

end HW.DbC;

--  vim: set ts=8 sts=3 sw=3 et:
