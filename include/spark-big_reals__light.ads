-----------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                      S P A R K . B I G _ R E A L S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2022-2022, AdaCore                     --
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

--  This unit is provided as a replacement for the standard unit
--  Ada.Numerics.Big_Numbers.Big_Reals when only proof with SPARK is
--  intended. It cannot be used for execution, as all subprograms are marked
--  imported with no definition.

--  Contrary to Ada.Numerics.Big_Numbers.Big_Reals, this unit does not
--  depend on System or Ada.Finalization, which makes it more convenient for
--  use in run-time units.

with Ada.Numerics.Big_Numbers; use Ada.Numerics.Big_Numbers;
with SPARK.Big_Integers;

package SPARK.Big_Reals with
   SPARK_Mode,
   Ghost
is
   pragma Annotate (GNATprove, Always_Return, Big_Reals);

   type Big_Real is private with
     Real_Literal => From_Universal_Image;

   function Is_Valid (Arg : Big_Real) return Boolean
   with
     Import,
     Global => null;

   subtype Valid_Big_Real is Big_Real
     with Dynamic_Predicate => Is_Valid (Valid_Big_Real),
          Predicate_Failure => raise Program_Error;

   function "/"
     (Num, Den : SPARK.Big_Integers.Valid_Big_Integer) return Valid_Big_Real
   with
     Import,
     Global => null;

   function Numerator
     (Arg : Valid_Big_Real) return Big_Integers.Valid_Big_Integer
   with
     Import,
     Global => null;

   function Denominator (Arg : Valid_Big_Real) return Big_Integers.Big_Positive
   with
     Import,
     Post   =>
       (if Arg = To_Real (0)
        then Big_Integers."=" (Denominator'Result,
                               Big_Integers.To_Big_Integer (1))
        else Big_Integers."="
               (Big_Integers.Greatest_Common_Divisor
                 (Numerator (Arg), Denominator'Result),
                Big_Integers.To_Big_Integer (1))),
     Global => null;

   function To_Big_Real
     (Arg : Big_Integers.Big_Integer)
     return Valid_Big_Real is (Arg / Big_Integers.To_Big_Integer (1))
   with
     Global => null;

   function To_Real (Arg : Integer) return Valid_Big_Real is
     (Big_Integers.To_Big_Integer (Arg) / Big_Integers.To_Big_Integer (1))
   with
     Global => null;

   function "=" (L, R : Valid_Big_Real) return Boolean with
     Import,
     Global => null;

   function "<" (L, R : Valid_Big_Real) return Boolean with
     Import,
     Global => null;

   function "<=" (L, R : Valid_Big_Real) return Boolean with
     Import,
     Global => null;

   function ">" (L, R : Valid_Big_Real) return Boolean with
     Import,
     Global => null;

   function ">=" (L, R : Valid_Big_Real) return Boolean with
     Import,
     Global => null;

   function In_Range (Arg, Low, High : Big_Real) return Boolean is
     (Low <= Arg and then Arg <= High)
   with
     Global => null;

   generic
      type Num is digits <>;
   package Float_Conversions is

      function To_Big_Real (Arg : Num) return Valid_Big_Real with
        Global => null;

      function From_Big_Real (Arg : Big_Real) return Num with
        Pre    => In_Range (Arg,
                            Low  => To_Big_Real (Num'First),
                            High => To_Big_Real (Num'Last))
                   or else (raise Constraint_Error),
        Global => null;

   end Float_Conversions;

   generic
      type Num is delta <>;
   package Fixed_Conversions is

      function To_Big_Real (Arg : Num) return Valid_Big_Real with
        Global => null;

      function From_Big_Real (Arg : Big_Real) return Num with
        Pre    => In_Range (Arg,
                            Low  => To_Big_Real (Num'First),
                            High => To_Big_Real (Num'Last))
                   or else (raise Constraint_Error),
        Global => null;

   end Fixed_Conversions;

   function To_String (Arg  : Valid_Big_Real;
                       Fore : Field := 2;
                       Aft  : Field := 3;
                       Exp  : Field := 0) return String
   with
     Import,
     Post   => To_String'Result'First = 1,
     Global => null;

   function From_String (Arg : String) return Valid_Big_Real with
     Import,
     Global => null;

   function From_Universal_Image (Arg : String) return Valid_Big_Real
     renames From_String;
   function From_Universal_Image (Num, Den : String) return Valid_Big_Real is
     (Big_Integers.From_Universal_Image (Num) /
      Big_Integers.From_Universal_Image (Den))
   with
     Global => null;

   function From_Quotient_String (Arg : String) return Valid_Big_Real
   with
     Import,
     Global => null;

   function "+" (L : Valid_Big_Real) return Valid_Big_Real
   with
     Import,
     Global => null;

   function "-" (L : Valid_Big_Real) return Valid_Big_Real
   with
     Import,
     Global => null;

   function "abs" (L : Valid_Big_Real) return Valid_Big_Real
   with
     Import,
     Global => null;

   function "+" (L, R : Valid_Big_Real) return Valid_Big_Real
   with
     Import,
     Global => null;

   function "-" (L, R : Valid_Big_Real) return Valid_Big_Real
   with
     Import,
     Global => null;

   function "*" (L, R : Valid_Big_Real) return Valid_Big_Real
   with
     Import,
     Global => null;

   function "/" (L, R : Valid_Big_Real) return Valid_Big_Real
   with
     Import,
     Global => null;

   function "**" (L : Valid_Big_Real; R : Integer) return Valid_Big_Real
   with
     Import,
     Global => null;

   function Min (L, R : Valid_Big_Real) return Valid_Big_Real
   with
     Import,
     Global => null;

   function Max (L, R : Valid_Big_Real) return Valid_Big_Real with
     Import,
     Global => null;

private
   pragma SPARK_Mode (Off);

   type Big_Real is null record;

end SPARK.Big_Reals;
