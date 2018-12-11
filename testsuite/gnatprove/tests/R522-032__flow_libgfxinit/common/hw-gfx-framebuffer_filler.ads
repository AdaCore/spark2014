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

with System;

with HW;

use type HW.Int32;

package HW.GFX.Framebuffer_Filler
is

   procedure Fill (Linear_FB : Word64; Framebuffer : Framebuffer_Type)
   with
      Pre =>
         Framebuffer.Width <= Framebuffer.Stride;

end HW.GFX.Framebuffer_Filler;
