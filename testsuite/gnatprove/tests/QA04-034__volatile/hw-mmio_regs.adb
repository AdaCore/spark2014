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

package body HW.MMIO_Regs
is

   generic
      type Word_T is mod <>;
   procedure Read_G (Value : out Word_T; Idx : Subs_P.Index_T);

   procedure Read_G (Value : out Word_T; Idx : Subs_P.Index_T)
   is
      Off : constant Range_P.Index_T := Range_P.Index_T
        ((Byte_Offset + Regs (Idx).Byte_Offset) / (Range_P.Element_T'Size / 8));
      pragma Warnings
        (GNAT, Off, """Mask"" is not modified, could be declared constant",
         Reason => "Ada RM forbids making it constant.");
      Mask : Word64 := Shift_Left (1, Regs (Idx).MSB + 1 - Regs (Idx).LSB) - 1;
      pragma Warnings
        (GNAT, On, """Mask"" is not modified, could be declared constant");
      Temp : Range_P.Element_T;
   begin
      Range_P.Read (Temp, Off);
      Value := Word_T (Shift_Right (Word64 (Temp), Regs (Idx).LSB) and Mask);
   end Read_G;

   procedure Read_I is new Read_G (Word8);
   procedure Read (Value : out Word8; Idx : Subs_P.Index_T) renames Read_I;

   procedure Read_I is new Read_G (Word16);
   procedure Read (Value : out Word16; Idx : Subs_P.Index_T) renames Read_I;

   procedure Read_I is new Read_G (Word32);
   procedure Read (Value : out Word32; Idx : Subs_P.Index_T) renames Read_I;

   procedure Read_I is new Read_G (Word64);
   procedure Read (Value : out Word64; Idx : Subs_P.Index_T) renames Read_I;

   ----------------------------------------------------------------------------

   generic
      type Word_T is mod <>;
   procedure Write_G (Idx : Subs_P.Index_T; Value : Word_T);

   procedure Write_G (Idx : Subs_P.Index_T; Value : Word_T)
   is
      Off : constant Range_P.Index_T := Range_P.Index_T
        ((Byte_Offset + Regs (Idx).Byte_Offset) / (Range_P.Element_T'Size / 8));
      pragma Warnings
        (GNAT, Off, """Mask"" is not modified, could be declared constant",
         Reason => "Ada RM forbids making it constant.");
      Mask : Word64 :=
         Shift_Left (1, Regs (Idx).MSB + 1) - Shift_Left (1, Regs (Idx).LSB);
      pragma Warnings
        (GNAT, On, """Mask"" is not modified, could be declared constant");
      Temp : Range_P.Element_T;
   begin
      if Regs (Idx).MSB - Regs (Idx).LSB + 1 = Range_P.Element_T'Size then
         Range_P.Write (Off, Range_P.Element_T (Value));
      else
         -- read/modify/write
         Range_P.Read (Temp, Off);
         Temp := Range_P.Element_T
           ((Word64 (Temp) and not Mask) or
            (Shift_Left (Word64 (Value), Regs (Idx).LSB)));
         Range_P.Write (Off, Temp);
      end if;
   end Write_G;

   procedure Write_I is new Write_G (Word8);
   procedure Write (Idx : Subs_P.Index_T; Value : Word8) renames Write_I;

   procedure Write_I is new Write_G (Word16);
   procedure Write (Idx : Subs_P.Index_T; Value : Word16) renames Write_I;

   procedure Write_I is new Write_G (Word32);
   procedure Write (Idx : Subs_P.Index_T; Value : Word32) renames Write_I;

   procedure Write_I is new Write_G (Word64);
   procedure Write (Idx : Subs_P.Index_T; Value : Word64) renames Write_I;

end HW.MMIO_Regs;
