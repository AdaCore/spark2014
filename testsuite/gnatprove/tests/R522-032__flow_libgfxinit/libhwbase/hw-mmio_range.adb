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

package body HW.MMIO_Range
with
   Refined_State =>
     (State => MMIO,
      Base_Address => null)
is

   MMIO : Array_T with Volatile, Address => System'To_Address (Base_Addr);

   procedure Read (Value : out Element_T; Index : in Index_T) is
   begin
      Value := MMIO (Index);
   end Read;

   procedure Write (Index : in Index_T; Value : in Element_T) is
   begin
      MMIO (Index) := Value;
   end Write;

   procedure Set_Base_Address (Base : Word64) is null;

end HW.MMIO_Range;
