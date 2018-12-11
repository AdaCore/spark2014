--
-- Copyright (C) 2017 Nico Huber <nico.h@gmx.de>
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

package HW.Config
is

   Dynamic_MMIO : constant Boolean := False;

   Default_MMConf_Base : constant := 16#f000_0000#;

   ----------------------------------------------------------------------------

   Default_MMConf_Base_Set : constant Boolean := Default_MMConf_Base /= 0;

end HW.Config;
