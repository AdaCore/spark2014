------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--           S P A R K . M O D _ A R I T H M E T I C _ L E M M A S          --
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
   type Uint is mod <>;
package SPARK.Mod_Arithmetic_Lemmas
  with SPARK_Mode
--  ??? Commenting out Ghost aspect for now until frontend accepts it
--       Ghost
is
   pragma Warnings
     (Off, "postcondition does not check the outcome of calling");

   subtype Pos is Uint range 1 .. Uint'Last;

   procedure Lemma_Mult_Is_Monotonic
     (Val1   : Uint;
      Val2   : Uint;
      Factor : Pos)
   with
     Global => null,
     Pre  => Val1 < Val2 and then
             Val2 <= Uint'Last / Factor,
     Post => Val1 * Factor < Val2 * Factor;

   procedure Lemma_Mult_Protect
     (Arg1        : Uint;
      Arg2        : Uint;
      Upper_Bound : Uint)
   with
     Global => null,
     Pre  => Arg2 = 0 or else Arg1 <= Upper_Bound / Arg2,
     Post => Arg1 * Arg2 <= Upper_Bound;

   procedure Lemma_Mult_Scale
     (Val         : Uint;
      Scale_Num   : Uint;
      Scale_Denom : Pos;
      Res         : Uint)
   with
     Global => null,
     Pre  => Scale_Num <= Scale_Denom and then
             (Scale_Num = 0 or else Val <= Uint'Last / Scale_Num) and then
             Res = (Val * Scale_Num) / Scale_Denom,
     Post => Res <= Val;

   procedure Lemma_Div_Is_Monotonic
     (Val1  : Uint;
      Val2  : Uint;
      Denom : Pos)
   with
     Global => null,
     Pre  => Val1 <= Val2,
     Post => Val1 / Denom <= Val2 / Denom;

   procedure Lemma_Mult_Then_Div_Is_Ident
     (Arg1 : Uint;
      Arg2 : Pos)
   with
     Global => null,
     Pre  => Arg1 <= Uint'Last / Arg2,
     Post => (Arg1 * Arg2) / Arg2 = Arg1;

   procedure Lemma_Div_Then_Mult
     (Arg1 : Uint;
      Arg2 : Pos)
   with
     Global => null,
     Post => (Arg1 / Arg2) * Arg2 <= Arg1;

end SPARK.Mod_Arithmetic_Lemmas;
