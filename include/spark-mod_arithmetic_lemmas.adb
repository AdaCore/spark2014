------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--           S P A R K . M O D _ A R I T H M E T I C _ L E M M A S          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2016, AdaCore                        --
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

package body SPARK.Mod_Arithmetic_Lemmas
  with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
  On
#else
  Off
#end if;
is

   procedure Lemma_Div_Is_Monotonic
     (Val1  : Uint;
      Val2  : Uint;
      Denom : Pos)
   is null;

   procedure Lemma_Div_Then_Mult_Bounds
     (Arg1 : Uint;
      Arg2 : Pos;
      Res  : Uint)
   is
   begin
      pragma Assert (Res <= Arg1);  --  proved by altergo now
      pragma Assert (Arg1 - Res < Arg2); -- proved by altergo now
   end Lemma_Div_Then_Mult_Bounds;

   procedure Lemma_Mult_Is_Monotonic
     (Val1   : Uint;
      Val2   : Uint;
      Factor : Uint)
   is null;

   procedure Lemma_Mult_Is_Strictly_Monotonic
     (Val1   : Uint;
      Val2   : Uint;
      Factor : Pos)
   is null;

   procedure Lemma_Mult_Protect
     (Arg1        : Uint;
      Arg2        : Uint;
      Upper_Bound : Uint)
   is null;

   procedure Lemma_Mult_Scale
     (Val         : Uint;
      Scale_Num   : Uint;
      Scale_Denom : Pos;
      Res         : Uint)
   is null;

   procedure Lemma_Mult_Then_Div_Is_Ident
     (Arg1 : Uint;
      Arg2 : Pos)
   is null;

   procedure Lemma_Mult_Then_Mod_Is_Zero
     (Arg1 : Uint;
      Arg2 : Pos)
   is null;

end SPARK.Mod_Arithmetic_Lemmas;
