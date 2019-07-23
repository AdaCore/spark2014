pragma Ada_2012;
pragma Style_Checks (Off);
pragma SPARK_Mode;

with Interfaces.C; use Interfaces.C;
with Interfaces.C.Extensions;

package types is

  --
  --  Copyright (c) 2017 Jean-Christophe Dubois
  --  All rights reserved.
  --
  --  This program is free software; you can redistribute it and/or modify
  --  it under the terms of the GNU General Public License as published by
  --  the Free Software Foundation; either version 2, or (at your option)
  --  any later version.
  --
  --  This program is distributed in the hope that it will be useful,
  --  but WITHOUT ANY WARRANTY; without even the implied warranty of
  --  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  --  GNU General Public License for more details.
  --
  --  You should have received a copy of the GNU General Public License
  --  along with this program; if not, write to the Free Software
  --  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
  --
  --  @file
  --  @author Jean-Christophe Dubois (jcd@tribudubois.net)
  --  @brief
  --

   subtype uint8_t is unsigned_char;

   subtype uint16_t is unsigned_short;

   subtype uint32_t is unsigned;

   subtype uint64_t is Extensions.unsigned_long_long;

   subtype int8_t is signed_char;

   subtype int16_t is short;

   subtype int32_t is int;

   subtype int64_t is Extensions.long_long;

   subtype size_t is unsigned;

   subtype intptr_t is unsigned_long;

end types;
