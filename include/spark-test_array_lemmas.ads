------------------------------------------------------------------------------
--                                                                          --
--                         SPARK LIBRARY COMPONENTS                         --
--                                                                          --
--              S P A R K . T E S T _ A R R A Y _ L E M M A S               --
--                                                                          --
--                                 S p e c                                  --
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

package SPARK.Test_Array_Lemmas
  with SPARK_Mode
is
   pragma Warnings
     (Off, "postcondition does not check the outcome of calling");

   type Index_Type is range 1 .. 10;
   type Arr_Int_Constrained is array (Index_Type) of Integer;
   type Arr_Float_Constrained is array (Index_Type) of Float;

   procedure Test_Transitive_Order_Int (Arr : Arr_Int_Constrained) with
     Global => null,
     Pre =>
       (for all I in Index_Type'First + 1 .. Index_Type'Last =>
          (Arr (I - 1) < Arr (I))),
     Post => (for all I in Arr'Range =>
                (for all J in Arr'Range =>
                     (if I < J then Arr (I) < Arr (J))));

   procedure Test_Transitive_Order_Float (Arr : Arr_Float_Constrained) with
     Global => null,
     Pre =>
       (for all I in Index_Type'First + 1 .. Index_Type'Last =>
          (Arr (I - 1) < Arr (I))),
     Post => (for all I in Arr'Range =>
                (for all J in Arr'Range =>
                     (if I < J then Arr (I) < Arr (J))));

   type Arr_Int_Unconstrained is array (Integer range <>) of Integer;
   type Arr_Float_Unconstrained is array (Integer range <>) of Float;

   procedure Test_Transitive_Order_Int (Arr : Arr_Int_Unconstrained) with
     Global => null,
     Pre =>
       (for all I in Arr'First + 1 .. Arr'Last =>
          (Arr (I - 1) < Arr (I))),
     Post => (for all I in Arr'Range =>
                (for all J in Arr'Range =>
                     (if I < J then Arr (I) < Arr (J))));

   procedure Test_Transitive_Order_Float (Arr : Arr_Float_Unconstrained) with
     Global => null,
     Pre =>
       (for all I in Arr'First + 1 .. Arr'Last =>
          (Arr (I - 1) < Arr (I))),
     Post => (for all I in Arr'Range =>
                (for all J in Arr'Range =>
                     (if I < J then Arr (I) < Arr (J))));

end SPARK.Test_Array_Lemmas;
