------------------------------------------------------------------------------
--                                                                          --
--                         GNAT RUN-TIME COMPONENTS                         --
--                                                                          --
--                ADA.NUMERICS.GENERIC_ELEMENTARY_FUNCTIONS                 --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2012-2013, Free Software Foundation, Inc.         --
--                                                                          --
-- This specification is derived from the Ada Reference Manual for use with --
-- GNAT. The copyright notice above, and the license provisions that follow --
-- apply solely to the Post aspects that have been added to the spec.       --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
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
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

package Formal.Numerics.Elementary_Functions with
  SPARK_Mode
is
   pragma Pure;
   pragma Annotate (GNATprove, Terminating, Elementary_Functions);

   function Sqrt (X : Float) return Float with
     Pre => X >= 0.0,
     Post => Sqrt'Result >= 0.0
               and then (if X = 0.0 then Sqrt'Result = 0.0)
               and then (if X = 1.0 then Sqrt'Result = 1.0);

   function Log (X : Float) return Float with
     Pre => X > 0.0,
     Post => (if X = 1.0 then Log'Result = 0.0);

   function Log (X, Base : Float) return Float with
     Pre => X > 0.0 and (Base > 0.0 and then Base /= 1.0),
     Post => (if X = 1.0 then Log'Result = 0.0);

   function Exp (X : Float) return Float with
     Post => (if X = 0.0 then Exp'Result = 1.0);

   function "**" (Left, Right : Float) return Float with
     Pre => (Left = 0.0 and then Right > 0.0) or
            (Left > 0.0 and then Right /= 0.0),
     Post => "**"'Result >= 0.0
               and then (if Right = 0.0 then "**"'Result = 1.0)
               and then (if Right = 1.0 then "**"'Result = Left)
               and then (if Left = 1.0 then "**"'Result = 1.0)
               and then (if Left = 0.0 then "**"'Result = 0.0);

   function Sin (X : Float) return Float with
     Post => Sin'Result in -1.0 .. 1.0
               and then (if X = 0.0 then Sin'Result = 0.0);

   function Sin (X, Cycle : Float) return Float with
     Pre => Cycle > 0.0,
     Post => Sin'Result in -1.0 .. 1.0
               and then (if X = 0.0 then Sin'Result = 0.0);

   function Cos (X : Float) return Float with
     Post => Cos'Result in -1.0 .. 1.0
               and then (if X = 0.0 then Cos'Result = 1.0);

   function Cos (X, Cycle : Float) return Float with
     Pre => Cycle > 0.0,
     Post => Cos'Result in -1.0 .. 1.0
               and then (if X = 0.0 then Cos'Result = 1.0);

   function Tan (X : Float) return Float with
     Post => (if X = 0.0 then Tan'Result = 0.0);

   function Tan (X, Cycle : Float) return Float with
     Pre => Cycle > 0.0 and then
            abs Float'Remainder (X, Cycle) /= 0.25 * Cycle,
     Post => (if X = 0.0 then Tan'Result = 0.0);

   function Cot (X : Float) return Float with
     Pre => X /= 0.0;

   function Cot (X, Cycle : Float) return Float with
     Pre => Cycle > 0.0 and then
            X /= 0.0 and then
            abs (Float'Remainder(X,Cycle)) /= 0.5 * Cycle;

   function Arcsin (X : Float) return Float with
     Pre => abs X <= 1.0,
     Post => (if X = 0.0 then Arcsin'Result = 0.0);

   function Arcsin (X, Cycle : Float) return Float with
     Pre => abs X <= 1.0 and then Cycle > 0.0,
     Post => (if X = 0.0 then Arcsin'Result = 0.0);

   function Arccos (X : Float) return Float with
     Pre => abs X <= 1.0,
     Post => (if X = 1.0 then Arccos'Result = 0.0);

   function Arccos (X, Cycle : Float) return Float with
     Pre => abs X <= 1.0 and then Cycle > 0.0,
     Post => (if X = 1.0 then Arccos'Result = 0.0);

   function Arctan
     (Y : Float;
      X : Float := 1.0) return Float
   with
     Pre => X /= 0.0 or Y /= 0.0,
     Post => (if X > 0.0 and Y = 0.0 then Arctan'Result = 0.0);

   function Arctan
     (Y     : Float;
      X     : Float := 1.0;
      Cycle : Float) return Float
   with
     Pre => (X /= 0.0 or Y /= 0.0) and then Cycle > 0.0,
     Post => (if X > 0.0 and Y = 0.0 then Arctan'Result = 0.0);

   function Arccot
     (X   : Float;
      Y   : Float := 1.0) return Float
   with
     Pre => X /= 0.0 or Y /= 0.0,
     Post => (if X > 0.0 and Y = 0.0 then Arccot'Result = 0.0);

   function Arccot
     (X     : Float;
      Y     : Float := 1.0;
      Cycle : Float) return Float
   with
     Pre => (X /= 0.0 or Y /= 0.0) and then Cycle > 0.0,
     Post => (if X > 0.0 and Y = 0.0 then Arccot'Result = 0.0);

   function Sinh (X : Float) return Float with
     Post => (if X = 0.0 then Sinh'Result = 0.0);

   function Cosh (X : Float) return Float with
     Post => Cosh'Result >= 1.0
               and then (if X = 0.0 then Cosh'Result = 1.0);

   function Tanh (X : Float) return Float with
     Post => Tanh'Result in -1.0 .. 1.0
               and then (if X = 0.0 then Tanh'Result = 0.0);

   function Coth (X : Float) return Float with
     Pre => X /= 0.0,
     Post => abs Coth'Result >= 1.0;

   function Arcsinh (X : Float) return Float with
     Post => (if X = 0.0 then Arcsinh'Result = 0.0);

   function Arccosh (X : Float) return Float with
     Pre => X >= 1.0,
     Post => Arccosh'Result >= 0.0
               and then (if X = 1.0 then Arccosh'Result = 0.0);

   function Arctanh (X : Float) return Float with
     Pre => abs X < 1.0,
     Post => (if X = 0.0 then Arctanh'Result = 0.0);

   function Arccoth (X : Float) return Float with
     Pre => abs X > 1.0;

end Formal.Numerics.Elementary_Functions;
