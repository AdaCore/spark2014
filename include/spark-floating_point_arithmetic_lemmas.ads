------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                                S P A R K .                               --
--      F L O A T I N G _ P O I N T _ A R I T H M E T I C _ L E M M A S     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2017-2019, AdaCore                     --
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

--  This unit defines floating-point lemmas in a generic way, subject to the
--  definition of the following generic parameters:
--    Fl is a floating-point type
--    Fl_Last_Sqrt is a value whose square does not overflow the base type
--      of Fl, which is used to bound inputs in precondition of some lemmas
--
--  The SPARK lemma library comes with two instances of this generic unit, for
--  32bits and 64bits floating-point types. Both instances have been completely
--  proved, using manual proof in Coq where needed. It is recommended to use
--  these instances instead of instantiating your own version of the generic,
--  in order to benefit from the proofs already done on the existing instances.

generic
   type Fl is digits <>;
   Fl_Last_Sqrt : Fl;
package SPARK.Floating_Point_Arithmetic_Lemmas
  with SPARK_Mode,
       Pure,
       Ghost
is
   pragma Annotate (GNATprove, Terminating, Floating_Point_Arithmetic_Lemmas);

   pragma Warnings
     (Off, "postcondition does not check the outcome of calling");

   procedure Lemma_Add_Is_Monotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
   with
       Global => null,
       Pre =>
         (Val1 in Fl'First / 2.0 .. Fl'Last / 2.0) and then
         (Val2 in Fl'First / 2.0 .. Fl'Last / 2.0) and then
         (Val3 in Fl'First / 2.0 .. Fl'Last / 2.0) and then
          Val1 <= Val2,
       Post => Val1 + Val3 <= Val2 + Val3;

   procedure Lemma_Sub_Is_Monotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
     with
       Global => null,
       Pre =>
         (Val1 in Fl'First / 2.0 .. Fl'Last / 2.0) and then
         (Val2 in Fl'First / 2.0 .. Fl'Last / 2.0) and then
         (Val3 in Fl'First / 2.0 .. Fl'Last / 2.0) and then
         Val1 <= Val2,
       Post => Val1 - Val3 <= Val2 - Val3;

   procedure Lemma_Mul_Is_Monotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
     with
       Global => null,
       Pre =>
         (Val1 in -Fl_Last_Sqrt .. Fl_Last_Sqrt) and then
         (Val2 in -Fl_Last_Sqrt .. Fl_Last_Sqrt) and then
         (Val3 in 0.0 .. Fl_Last_Sqrt) and then
         Val1 <= Val2,
       Post => Val1 * Val3 <= Val2 * Val3;  --  MANUAL PROOF

   procedure Lemma_Mul_Is_Antimonotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
     with
       Global => null,
       Pre =>
         (Val1 in -Fl_Last_Sqrt .. Fl_Last_Sqrt) and then
         (Val2 in -Fl_Last_Sqrt .. Fl_Last_Sqrt) and then
         (Val3 in -Fl_Last_Sqrt .. 0.0) and then
         Val1 <= Val2,
       Post => Val2 * Val3 <= Val1 * Val3;  --  MANUAL PROOF

   procedure Lemma_Div_Is_Monotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
     with
       Global => null,
       Pre =>
         (Val1 in -Fl_Last_Sqrt .. Fl_Last_Sqrt) and then
         (Val2 in -Fl_Last_Sqrt .. Fl_Last_Sqrt) and then
         (Val3 in 1.0 / Fl_Last_Sqrt .. Fl'Last) and then
         Val1 <= Val2,
       Post => Val1 / Val3 <= Val2 / Val3;  --  MANUAL PROOF

   procedure Lemma_Div_Is_Antimonotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
     with
       Global => null,
       Pre =>
         (Val1 in -Fl_Last_Sqrt .. Fl_Last_Sqrt) and then
         (Val2 in -Fl_Last_Sqrt .. Fl_Last_Sqrt) and then
         (Val3 in Fl'First .. -1.0 / Fl_Last_Sqrt) and then
         Val1 <= Val2,
     Post => Val2 / Val3 <= Val1 / Val3;  --  MANUAL PROOF

end SPARK.Floating_Point_Arithmetic_Lemmas;
