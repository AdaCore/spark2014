------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                  S P A R K . H I G H E R _ O R D E R                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2020, AdaCore                     --
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

package body SPARK.Higher_Order with SPARK_Mode is

   ---------
   -- Map --
   ---------

   function Map (A : Array_In) return Array_Out is
      pragma Annotate
        (GNATprove, False_Positive,
         """R"" might not be initialized", "Array initialized in loop");
   begin
      return R : Array_Out (A'Range) do
         for I in A'Range loop
            R (I) := F (A (I));
            pragma Loop_Invariant (for all K in A'First .. I =>
                                     R (K) = F (A (K)));
         end loop;
      end return;
   end Map;

   -----------
   -- Map_I --
   -----------

   function Map_I (A : Array_In) return Array_Out is
      pragma Annotate
        (GNATprove, False_Positive,
         """R"" might not be initialized", "Array initialized in loop");
   begin
      return R : Array_Out (A'Range) do
         for I in A'Range loop
            R (I) := F (I, A (I));
            pragma Loop_Invariant (for all K in A'First .. I =>
                                     R (K) = F (K, A (K)));
         end loop;
      end return;
   end Map_I;

   ----------------
   -- Map_I_Proc --
   ----------------

   procedure Map_I_Proc (A : in out Array_Type) is
   begin
      for I in A'Range loop
         A (I) := F (I, A (I));
         pragma Loop_Invariant (for all K in A'First .. I =>
                                  A (K) = F (K, A'Loop_Entry (K)));
      end loop;
   end Map_I_Proc;

   --------------
   -- Map_Proc --
   --------------

   procedure Map_Proc (A : in out Array_Type) is
   begin
      for I in A'Range loop
         A (I) := F (A (I));
         pragma Loop_Invariant (for all K in A'First .. I =>
                                  A (K) = F (A'Loop_Entry (K)));
      end loop;
   end Map_Proc;

end SPARK.Higher_Order;
