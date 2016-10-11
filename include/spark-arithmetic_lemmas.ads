------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--              S P A R K . A R I T H M E T I C _ L E M M A S               --
--                                                                          --
--                                 S p e c                                  --
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

generic
   type Int is range <>;
package SPARK.Arithmetic_Lemmas
  with SPARK_Mode,
       Pure,
       Ghost
is
   pragma Warnings
     (Off, "postcondition does not check the outcome of calling");

   subtype Nat is Int range 0 .. Int'Last;
   subtype Pos is Int range 1 .. Int'Last;

   procedure Lemma_Div_Is_Monotonic
     (Val1  : Int;
      Val2  : Int;
      Denom : Pos)
   with
     Global => null,
     Pre  => Val1 <= Val2,
     Post => Val1 / Denom <= Val2 / Denom;  --  MANUAL PROOF

   procedure Lemma_Mod_Range
     (Arg1 : Int;
      Arg2 : Pos)
   with
     Global => null,
     Post => Arg1 mod Arg2 in 0 .. Arg2 - 1;

   procedure Lemma_Mod_Symmetry
     (Arg1 : Int;
      Arg2 : Int)
   with
     Global => null,
     Pre  => Arg2 /= 0,
     Post => (-Arg1) mod (-Arg2) = -(Arg1 mod Arg2);  --  MANUAL PROOF

   procedure Lemma_Mult_Is_Monotonic
     (Val1   : Int;
      Val2   : Int;
      Factor : Nat)
   with
     Global => null,
     Pre  => Val1 <= Val2,
     Post => Val1 * Factor <= Val2 * Factor;  --  MANUAL PROOF

   procedure Lemma_Mult_Is_Strictly_Monotonic
     (Val1   : Int;
      Val2   : Int;
      Factor : Pos)
   with
     Global => null,
     Pre  => Val1 < Val2,
     Post => Val1 * Factor < Val2 * Factor;  --  MANUAL PROOF

   procedure Lemma_Mult_Protect
     (Arg1        : Int;
      Arg2        : Nat;
      Upper_Bound : Nat)
   with
     Global => null,
     Pre  => Arg2 = 0 or else Arg1 <= Upper_Bound / Arg2,
     Post => Arg1 * Arg2 <= Upper_Bound;

   procedure Lemma_Mult_Scale
     (Val         : Int;
      Scale_Num   : Nat;
      Scale_Denom : Pos;
      Res         : Int)
   with
     Global => null,
     Pre  => Scale_Num <= Scale_Denom and then
             Res = (Val * Scale_Num) / Scale_Denom,
     Post => abs (Res) <= abs (Val) and then
             (if Val >= 0 then Res >= 0 else Res <= 0);

   procedure Lemma_Mult_Then_Mod_Is_Zero
     (Arg1 : Int;
      Arg2 : Pos)
   with
     Global => null,
     Post => (Arg1 * Arg2) mod Arg2 = 0;

end SPARK.Arithmetic_Lemmas;
