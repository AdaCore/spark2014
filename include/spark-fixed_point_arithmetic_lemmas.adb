------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                                S P A R K .                               --
--        F I X E D _ P O I N T _ A R I T H M E T I C _ L E M M A S         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2018, AdaCore                        --
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

package body SPARK.Fixed_Point_Arithmetic_Lemmas is

   procedure GNAT_Lemma_Div_Is_Monotonic
     (Num1  : Fix;
      Num2  : Fix;
      Denom : Positive)
   is null;

   procedure GNAT_Lemma_Div_Right_Is_Monotonic
     (Num    : Fix;
      Denom1 : Positive;
      Denom2 : Positive)
   is null;

   procedure GNAT_Lemma_Mult_Then_Div_Is_Ident
     (Val1 : Fix;
      Val2 : Positive)
   is null;

end SPARK.Fixed_Point_Arithmetic_Lemmas;
