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

with HW.GFX.I2C;

private package HW.GFX.GMA.I2C is

   procedure I2C_Read
     (Port     : in     PCH_Port;
      Address  : in     HW.GFX.I2C.Transfer_Address;
      Length   : in out HW.GFX.I2C.Transfer_Length;
      Data     :    out HW.GFX.I2C.Transfer_Data;
      Success  :    out Boolean);

end HW.GFX.GMA.I2C;
