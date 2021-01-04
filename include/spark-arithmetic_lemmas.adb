------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--              S P A R K . A R I T H M E T I C _ L E M M A S               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2016-2021, AdaCore                     --
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

package body SPARK.Arithmetic_Lemmas
  with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
  On
#else
  Off
#end if;
is

   procedure Lemma_Div_Is_Monotonic
     (Val1  : Int;
      Val2  : Int;
      Denom : Pos)
   is null;

   procedure Lemma_Div_Right_Is_Monotonic
     (Num    : Int;
      Denom1 : Pos;
      Denom2 : Pos)
   is null;

   procedure Lemma_Exp_Is_Monotonic
     (Val1 : Nat;
      Val2 : Nat;
      Exp  : Natural)
   is null;

   procedure Lemma_Exp_Is_Monotonic_2
     (Val  : Pos;
      Exp1 : Natural;
      Exp2 : Natural)
   is null;

   procedure Lemma_Mod_Range
     (Arg1 : Int;
      Arg2 : Pos)
   is null;

   procedure Lemma_Mod_Symmetry
     (Arg1 : Int;
      Arg2 : Int)
   is null;

   procedure Lemma_Mult_Is_Monotonic
     (Val1   : Int;
      Val2   : Int;
      Factor : Nat)
   is null;

   procedure Lemma_Mult_Is_Strictly_Monotonic
     (Val1   : Int;
      Val2   : Int;
      Factor : Pos)
   is null;

   procedure Lemma_Mult_Protect
     (Arg1        : Int;
      Arg2        : Nat;
      Upper_Bound : Nat)
   is null;

   procedure Lemma_Mult_Scale
     (Val         : Int;
      Scale_Num   : Nat;
      Scale_Denom : Pos;
      Res         : Int)
   is
   begin
      if Res >= 0 then
         pragma Assert (abs (Big (Res)) <= abs (Big (Val)));
      else
         pragma Assert (abs (Big (Res)) <= abs (Big (Val)));
      end if;
   end Lemma_Mult_Scale;

   procedure Lemma_Mult_Then_Div_Is_Ident
     (Val1 : Int;
      Val2 : Pos)
   is null;

   procedure Lemma_Mult_Then_Mod_Is_Zero
     (Arg1 : Int;
      Arg2 : Pos)
   is null;

end SPARK.Arithmetic_Lemmas;
