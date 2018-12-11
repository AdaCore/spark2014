--
-- Copyright (C) 2015-2016 secunet Security Networks AG
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

with HW.Config;
with HW.MMIO_Range;
pragma Elaborate_All (HW.MMIO_Range);

package body HW.GFX.Framebuffer_Filler
is

   type FB_Index is new Natural range
      0 .. Natural (Width_Type'Last * Height_Type'Last) - 1;
   type FB_Range is array (FB_Index) of Word32 with Pack;
   package FB is new MMIO_Range (0, Word32, FB_Index, FB_Range);

   procedure Fill (Linear_FB : Word64; Framebuffer : Framebuffer_Type)
   is
      Line_Start : Int32 := 0;
   begin
      if not HW.Config.Dynamic_MMIO then
         return;
      end if;

      FB.Set_Base_Address (Linear_FB);
      for Line in 0 .. Framebuffer.Height - 1 loop
         pragma Loop_Invariant (Line_Start = Line * Framebuffer.Stride);
         for Col in 0 .. Framebuffer.Width - 1 loop
            pragma Loop_Invariant (Line_Start = Line * Framebuffer.Stride);
            FB.Write (FB_Index (Line_Start + Col), 16#ff000000#);
         end loop;
         Line_Start := Line_Start + Framebuffer.Stride;
      end loop;
   end Fill;

end HW.GFX.Framebuffer_Filler;
