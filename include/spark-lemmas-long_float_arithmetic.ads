------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--   S P A R K . L E M M A S . L O N G _ F L O A T _ A R I T H M E T I C    --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2017-2022, AdaCore                     --
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
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Numerics.Big_Numbers.Big_Reals;
use  Ada.Numerics.Big_Numbers.Big_Reals;
with SPARK.Conversions.Long_Float_Conversions;
use SPARK.Conversions.Long_Float_Conversions;
with SPARK.Lemmas.Floating_Point_Arithmetic;

pragma Elaborate_All (SPARK.Lemmas.Floating_Point_Arithmetic);
package SPARK.Lemmas.Long_Float_Arithmetic is new
  SPARK.Lemmas.Floating_Point_Arithmetic
    (Fl           => Long_Float,
     Int          => Long_Integer,
     Fl_Last_Sqrt => 2.0 ** 511,
     Max_Int      => 2 ** 53,
     Epsilon      => 2.0 ** (-53),
     Eta          => 2.0 ** (-1075),
     Real         => To_Big_Real);
