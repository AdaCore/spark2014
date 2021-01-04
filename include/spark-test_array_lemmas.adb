------------------------------------------------------------------------------
--                                                                          --
--                         SPARK LIBRARY COMPONENTS                         --
--                                                                          --
--              S P A R K . T E S T _ A R R A Y _ L E M M A S               --
--                                                                          --
--                                 C o d e                                  --
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

with SPARK.Unconstrained_Array_Lemmas;
with SPARK.Constrained_Array_Lemmas;

package body SPARK.Test_Array_Lemmas
  with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
  On
#else
  Off
#end if;
is
   pragma Warnings
     (Off, "postcondition does not check the outcome of calling");

   package Test_Uint is new SPARK.Unconstrained_Array_Lemmas
     (Index_Type => Integer,
      Element_T  => Integer,
      A          => Arr_Int_Unconstrained,
      Less       => "<");

   package Test_Ufloat is new SPARK.Unconstrained_Array_Lemmas
     (Index_Type => Integer,
      Element_T  => Float,
      A          => Arr_Float_Unconstrained,
      Less       => "<");

   --  For now, constrained array need a type conversion. In the future,
   --  there will be a constrained array library.

   procedure Test_Transitive_Order_Float (Arr : Arr_Float_Constrained) is
   begin
      Test_Ufloat.Lemma_Transitive_Order
        (Arr_Float_Unconstrained (Arr));
   end Test_Transitive_Order_Float;

   procedure Test_Transitive_Order_Float
     (Arr : Arr_Float_Unconstrained) is
   begin
      Test_Ufloat.Lemma_Transitive_Order (Arr);
   end Test_Transitive_Order_Float;

   procedure Test_Transitive_Order_Int (Arr : Arr_Int_Constrained) is
   begin
      Test_Uint.Lemma_Transitive_Order
        (Arr_Int_Unconstrained (Arr));
   end Test_Transitive_Order_Int;

   procedure Test_Transitive_Order_Int (Arr : Arr_Int_Unconstrained) is
   begin
      Test_Uint.Lemma_Transitive_Order (Arr);
   end Test_Transitive_Order_Int;

end SPARK.Test_Array_Lemmas;
