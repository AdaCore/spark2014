------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--       S P A R K . C O N S T R A I N E D _ A R R A Y _ L E M M A S        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2016-2020, AdaCore                     --
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

--  ??? Do not work yet
with SPARK.Unconstrained_Array_Lemmas;

package body SPARK.Constrained_Array_Lemmas
  with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
  On
#else
  Off
#end if;
is

   type A_Unconstrained is array (Index_Type range <>) of Element_T;

   package Test is new SPARK.Unconstrained_Array_Lemmas
     (Index_Type => Index_Type,
      Element_T  => Element_T,
      A          => A_Unconstrained,
      Less       => Less);

   procedure Lemma_Transitive_Order (Arr : A) is
      Arr_T : constant A_Unconstrained := A_Unconstrained (Arr);
   begin
      Test.Lemma_Transitive_Order (Arr_T);
   end Lemma_Transitive_Order;

end SPARK.Constrained_Array_Lemmas;
