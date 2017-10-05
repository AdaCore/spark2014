--
-- Copyright (C) 2016 secunet Security Networks AG
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

with HW.Sub_Regs;
with HW.MMIO_Range;

use type HW.Word64;

generic
   with package Range_P is new MMIO_Range (<>);
   Byte_Offset_O : Natural := 0;

   with package Subs_P is new Sub_Regs (<>);
   Regs : Subs_P.Array_T;

package HW.MMIO_Regs
is

   Byte_Offset : Natural := Byte_Offset_O;

   ----------------------------------------------------------------------------

   procedure Read (Value : out Word8; Idx : Subs_P.Index_T)
   with
      Pre =>   ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) >= Integer (Range_P.Index_T'First) and
               ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) <= Integer (Range_P.Index_T'Last) and
               Range_P.Element_T'Size <= Word64'Size and
               Regs (Idx).MSB < Range_P.Element_T'Size and
               Regs (Idx).MSB >= Regs (Idx).LSB and
               Regs (Idx).MSB - Regs (Idx).LSB + 1 <= Word8'Size;

   procedure Read (Value : out Word16; Idx : Subs_P.Index_T)
   with
      Pre =>   ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) >= Integer (Range_P.Index_T'First) and
               ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) <= Integer (Range_P.Index_T'Last) and
               Range_P.Element_T'Size <= Word64'Size and
               Regs (Idx).MSB < Range_P.Element_T'Size and
               Regs (Idx).MSB >= Regs (Idx).LSB and
               Regs (Idx).MSB - Regs (Idx).LSB + 1 <= Word16'Size;

   procedure Read (Value : out Word32; Idx : Subs_P.Index_T)
   with
      Pre =>   ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) >= Integer (Range_P.Index_T'First) and
               ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) <= Integer (Range_P.Index_T'Last) and
               Range_P.Element_T'Size <= Word64'Size and
               Regs (Idx).MSB < Range_P.Element_T'Size and
               Regs (Idx).MSB >= Regs (Idx).LSB and
               Regs (Idx).MSB - Regs (Idx).LSB + 1 <= Word32'Size;

   procedure Read (Value : out Word64; Idx : Subs_P.Index_T)
   with
      Pre =>   ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) >= Integer (Range_P.Index_T'First) and
               ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) <= Integer (Range_P.Index_T'Last) and
               Range_P.Element_T'Size <= Word64'Size and
               Regs (Idx).MSB < Range_P.Element_T'Size and
               Regs (Idx).MSB >= Regs (Idx).LSB and
               Regs (Idx).MSB - Regs (Idx).LSB + 1 <= Word64'Size;

   ----------------------------------------------------------------------------

   procedure Write (Idx : Subs_P.Index_T; Value : Word8)
   with
      Pre =>   ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) >= Integer (Range_P.Index_T'First) and
               ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) <= Integer (Range_P.Index_T'Last) and
               Range_P.Element_T'Size <= Word64'Size and
               Regs (Idx).MSB < Range_P.Element_T'Size and
               Regs (Idx).MSB >= Regs (Idx).LSB and
               Regs (Idx).MSB - Regs (Idx).LSB + 1 <= Value'Size and
               Word64 (Value) < Word64 (2 ** (Regs (Idx).MSB + 1 - Regs (Idx).LSB));

   procedure Write (Idx : Subs_P.Index_T; Value : Word16)
   with
      Pre =>   ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) >= Integer (Range_P.Index_T'First) and
               ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) <= Integer (Range_P.Index_T'Last) and
               Range_P.Element_T'Size <= Word64'Size and
               Regs (Idx).MSB < Range_P.Element_T'Size and
               Regs (Idx).MSB >= Regs (Idx).LSB and
               Regs (Idx).MSB - Regs (Idx).LSB + 1 <= Value'Size and
               Word64 (Value) < Word64 (2 ** (Regs (Idx).MSB + 1 - Regs (Idx).LSB));

   procedure Write (Idx : Subs_P.Index_T; Value : Word32)
   with
      Pre =>   ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) >= Integer (Range_P.Index_T'First) and
               ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) <= Integer (Range_P.Index_T'Last) and
               Range_P.Element_T'Size <= Word64'Size and
               Regs (Idx).MSB < Range_P.Element_T'Size and
               Regs (Idx).MSB >= Regs (Idx).LSB and
               Regs (Idx).MSB - Regs (Idx).LSB + 1 <= Value'Size and
               Word64 (Value) < Word64 (2 ** (Regs (Idx).MSB + 1 - Regs (Idx).LSB));

   procedure Write (Idx : Subs_P.Index_T; Value : Word64)
   with
      Pre =>   ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) >= Integer (Range_P.Index_T'First) and
               ((Byte_Offset + Regs (Idx).Byte_Offset) /
                (Range_P.Element_T'Size / 8)) <= Integer (Range_P.Index_T'Last) and
               Range_P.Element_T'Size <= Word64'Size and
               Regs (Idx).MSB < Range_P.Element_T'Size and
               Regs (Idx).MSB >= Regs (Idx).LSB and
               Regs (Idx).MSB - Regs (Idx).LSB + 1 <= Value'Size and
               Word64 (Value) < Word64 (2 ** (Regs (Idx).MSB + 1 - Regs (Idx).LSB));

end HW.MMIO_Regs;
