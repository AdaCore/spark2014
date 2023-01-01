------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                   S P A R K . B I G _ I N T E G E R S                    --
--                                                                          --
--                                 B o d y                                  --
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

--  This body is provided as a work-around for a GNAT compiler bug, as GNAT
--  currently does not compile instantiations of the spec with imported ghost
--  generics for packages Signed_Conversions and Unsigned_Conversions.

package body SPARK.Big_Integers with
   SPARK_Mode => Off
is

   package body Signed_Conversions with
     SPARK_Mode => Off
   is

      function From_Big_Integer (Arg : Valid_Big_Integer) return Int is
      begin
         raise Program_Error;
         return 0;
      end From_Big_Integer;

      function To_Big_Integer (Arg : Int) return Valid_Big_Integer is
      begin
         raise Program_Error;
         return (null record);
      end To_Big_Integer;

   end Signed_Conversions;

   package body Unsigned_Conversions with
     SPARK_Mode => Off
   is

      function From_Big_Integer (Arg : Valid_Big_Integer) return Int is
      begin
         raise Program_Error;
         return 0;
      end From_Big_Integer;

      function To_Big_Integer (Arg : Int) return Valid_Big_Integer is
      begin
         raise Program_Error;
         return (null record);
      end To_Big_Integer;

   end Unsigned_Conversions;

end SPARK.Big_Integers;
