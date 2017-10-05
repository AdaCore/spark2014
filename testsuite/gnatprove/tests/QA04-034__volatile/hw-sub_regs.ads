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

generic
   type Index_T is (<>);
package HW.Sub_Regs is

   type T is record
      Byte_Offset : Natural;
      MSB    : Natural;
      LSB   : Natural;
   end record;

   type Array_T is array (Index_T) of T;

end HW.Sub_Regs;
