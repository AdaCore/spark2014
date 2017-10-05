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

with Libxhcidbg_Component.Memory;

private package HW.DbC.DMA_Buffers is

   Base : constant := Libxhcidbg_Component.Memory.Xhci_Dma_Address;

   --  First 64 * 4KiB are reserved for the transferred data.

   --  <dma_buffer name="Transfer_Rings" size="1024 * 2" align="16" />
   Transfer_Rings_Base           : constant := Base + 16#0004_0000#;

   --  <dma_buffer name="Event_Ring" size="1024" align="1024" />
   Event_Ring_Base               : constant := Base + 16#0004_0800#;

   --  <dma_buffer name="DbC_Context" size="64 * 3" align="64" />
   DbC_Context_Base              : constant := Base + 16#0004_0c00#;

   --  <dma_buffer name="Descriptor_Strings" size="32 * 4" align="1" />
   Descriptor_Strings_Base       : constant := Base + 16#0004_0cc0#;

   --  <dma_buffer name="Event_Ring_Segment_Table" size="16" align="64" />
   Event_Ring_Segment_Table_Base : constant := Base + 16#0004_0d40#;

end HW.DbC.DMA_Buffers;

--  vim: set ts=8 sts=3 sw=3 et:
