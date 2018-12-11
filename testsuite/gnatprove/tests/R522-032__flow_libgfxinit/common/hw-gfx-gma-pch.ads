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

with HW.GFX.GMA.Config;

private package HW.GFX.GMA.PCH is

   type FDI_Port_Type is (FDI_A, FDI_B, FDI_C);

   ----------------------------------------------------------------------------

   -- common to all PCH outputs

   PCH_TRANSCODER_SELECT_SHIFT : constant :=
     (case Config.CPU is
         when Ironlake                       => 30,
         when Sandybridge | Ivybridge        => 29,
         when others                         =>  0);

   PCH_TRANSCODER_SELECT_MASK : constant :=
     (case Config.CPU is
         when Ironlake                       => 1 * 2 ** 30,
         when Sandybridge | Ivybridge        => 3 * 2 ** 29,
         when others                         =>  0);

   type PCH_TRANSCODER_SELECT_Array is array (FDI_Port_Type) of Word32;
   PCH_TRANSCODER_SELECT : constant PCH_TRANSCODER_SELECT_Array :=
     (FDI_A => 0 * 2 ** PCH_TRANSCODER_SELECT_SHIFT,
      FDI_B => 1 * 2 ** PCH_TRANSCODER_SELECT_SHIFT,
      FDI_C => 2 * 2 ** PCH_TRANSCODER_SELECT_SHIFT);

end HW.GFX.GMA.PCH;
