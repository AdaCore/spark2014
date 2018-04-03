--  This proof was originally done by Claude Marché in Why3 and can be found
--  in the repository of Why3: examples/in_progres/isqrt_von_neumann

with Interfaces; use Interfaces;

package P
  with SPARK_Mode => On
is
   subtype Sqrt_Domain is Integer range 0 .. 2**31 - 1;
   subtype Sqrt_Range  is Integer range 0 .. 46340;

   subtype Sqrt_Domain16 is Integer range 0 .. 2**15 - 1;
   subtype Sqrt_Range16 is Integer range 0 .. 181;

   use type Interfaces.Unsigned_16;
   subtype U16 is Interfaces.Unsigned_16;

   --  truncated natural square root, Von Neumann's algorithm
   function Sqrt_Von_Neumann_Aux16 (X : in U16) return U16;


end P;
