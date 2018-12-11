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

package HW.GFX.GMA.PCH.Transcoder is

   procedure On
     (Port_Cfg : Port_Config;
      Port     : FDI_Port_Type;
      PLL      : Word32);

   procedure Off
     (Port  : FDI_Port_Type);

end HW.GFX.GMA.PCH.Transcoder;
