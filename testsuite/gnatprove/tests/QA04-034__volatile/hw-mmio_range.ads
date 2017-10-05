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

generic
   Base_Addr : Word64;
   type Element_T is mod <>;
   type Index_T is range <>;
   type Array_T is array (Index_T) of Element_T;
package HW.MMIO_Range
with
   Abstract_State =>
     ((State with External),
      Base_Address),
   Initializes => Base_Address
is

   procedure Read (Value : out Element_T; Index : in Index_T);

   procedure Write (Index : in Index_T; Value : in Element_T);

   procedure Set_Base_Address (Base : Word64);

end HW.MMIO_Range;
