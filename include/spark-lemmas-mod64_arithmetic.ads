------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--         S P A R K . L E M M A S . M O D 6 4 _ A R I T H M E T I C        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2016-2023, AdaCore                     --
--                                                                          --
-- SPARK is free software;  you can  redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. SPARK is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

pragma SPARK_Mode;
with SPARK.Lemmas.Mod_Arithmetic;
pragma Elaborate_All (SPARK.Lemmas.Mod_Arithmetic);
with Interfaces;
package SPARK.Lemmas.Mod64_Arithmetic is new
  SPARK.Lemmas.Mod_Arithmetic (Interfaces.Unsigned_64);
