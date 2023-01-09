------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                   S P A R K . B I G _ I N T E R V A L S                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2022-2023, AdaCore                     --
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

with SPARK.Big_Integers;
use  SPARK.Big_Integers;

package SPARK.Big_Intervals with SPARK_Mode, Ghost is
   --  Intervals of big integers to allow iteration. To be replaced by the
   --  appropriate library unit when there is one.

   type Interval is record
      First, Last : Big_Integer;
   end record
     with Iterable =>
       (First       => First,
        Next        => Next,
        Has_Element => In_Range);

   function First (I : Interval) return Big_Integer is
     (I.First);

   function Next (Dummy : Interval; X : Big_Integer) return Big_Integer is
     (X + 1);

   function In_Range (I : Interval; X : Big_Integer) return Boolean is
     (In_Range (X, I.First, I.Last));
end SPARK.Big_Intervals;
