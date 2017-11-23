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
   function Sqrt_Von_Neumann_Aux16 (X : in U16) return U16
     with Post => ((Sqrt_Von_Neumann_Aux16'Result *
                     Sqrt_Von_Neumann_Aux16'Result) <= X and
     --  In bitvectors, this postcondition is the correct one
                  (Sqrt_Von_Neumann_Aux16'Result + 1) *
                       (Sqrt_Von_Neumann_Aux16'Result + 1) - 1 >= X)
     and then
       (if X <= U16 (Sqrt_Domain16'Last) then
              Sqrt_Von_Neumann_Aux16'Result <= U16 (Sqrt_Range16'Last))
   ;


      --  truncated natural square root, Von Neumann's algorithm
   function Sqrt_Von_Neumann16 (X : in Sqrt_Domain16) return Sqrt_Range16
     with Post => (Sqrt_Von_Neumann16'Result *
                     Sqrt_Von_Neumann16'Result) <= X and
     (if Sqrt_Von_Neumann16'Result < Sqrt_Range16'Last then
        (Sqrt_Von_Neumann16'Result + 1) *
          (Sqrt_Von_Neumann16'Result + 1) > X);
   -- We could put (for all y in Sqrt_Range'Range => (if y > result then y ** 2 > x))


   --  truncated natural square root, Von Neumann's algorithm
--   function Sqrt_Von_Neumann (X : in Sqrt_Domain) return Sqrt_Range
--     with Post => (Sqrt_Von_Neumann'Result *
--                     Sqrt_Von_Neumann'Result) <= X and
--     (if Sqrt_Von_Neumann'Result < Sqrt_Range'Last then
--        (Sqrt_Von_Neumann'Result + 1) *
--          (Sqrt_Von_Neumann'Result + 1) > X);
   -- We could put (for all y in Sqrt_Range'Range => (if y > result then y ** 2 > x))

end P;
