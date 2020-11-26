------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                                S P A R K .                               --
--      F L O A T I N G _ P O I N T _ A R I T H M E T I C _ L E M M A S     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2017, AdaCore                        --
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

package body SPARK.Floating_Point_Arithmetic_Lemmas
  with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
  On
#else
  Off
#end if;
is
   procedure Lemma_Add_Is_Monotonic
        (Val1 : Fl;
         Val2 : Fl;
         Val3 : Fl)
   is null;

   procedure Lemma_Sub_Is_Monotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
   is null;

   procedure Lemma_Mult_Is_Monotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
   is null;

   procedure Lemma_Mult_Right_Negative_Is_Monotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
   is null;

   procedure Lemma_Div_Is_Monotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
   is null;

   procedure Lemma_Div_Right_Negative_Is_Monotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
   is null;

   procedure Lemma_Mult_By_Less_Than_One
     (Val1 : Fl;
      Val2 : Fl)
   is null;

   procedure Lemma_Div_Left_Is_Monotonic
     (Val1 : Float;
      Val2 : Float;
      Val3 : Float)
   is null;

end SPARK.Floating_Point_Arithmetic_Lemmas;
