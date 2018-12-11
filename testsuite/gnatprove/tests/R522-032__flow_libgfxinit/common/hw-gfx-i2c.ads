--
-- Copyright (C) 2015 secunet Security Networks AG
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

package HW.GFX.I2C is

   type Transfer_Address is mod 2 ** 7;
   subtype Transfer_Length is Natural range 0 .. 128;
   subtype Transfer_Index is Natural range 0 .. Transfer_Length'Last - 1;
   subtype Transfer_Data is Buffer (Transfer_Index);

end HW.GFX.I2C;
