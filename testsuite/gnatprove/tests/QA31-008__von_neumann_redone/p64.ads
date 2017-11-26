--  This proof was originally done by Claude Marché in Why3 and can be found
--  in the repository of Why3: examples/in_progres/isqrt_von_neumann

with Interfaces; use Interfaces;

package P64
  with SPARK_Mode => On
is
   subtype Sqrt_Domain64 is Long_Integer range 0 .. 2**63 - 1;
   subtype Sqrt_Range64  is Long_Integer range 0 .. 3037000499;

   use type Interfaces.Unsigned_64;
   subtype U64 is Interfaces.Unsigned_64;

   function Sqr (X : U64) return U64 is
     (X * X);

   procedure Lemma_Bv (X, Y : U64) with
     Ghost,
     Post => Sqr(X + Y) = Sqr(X) + Y * (2 * X + Y);

   --  truncated natural square root, Von Neumann's algorithm
   function Sqrt_Von_Neumann_Aux64 (X : in U64) return U64
     with Post => ((Sqrt_Von_Neumann_Aux64'Result *
                     Sqrt_Von_Neumann_Aux64'Result) <= X and
     --  In bitvectors, this postcondition is the correct one
                  (Sqrt_Von_Neumann_Aux64'Result + 1) *
                       (Sqrt_Von_Neumann_Aux64'Result + 1) - 1 >= X)
     and then
       (if X <= U64 (Sqrt_Domain64'Last) Then
              Sqrt_Von_Neumann_Aux64'Result <= U64 (Sqrt_Range64'Last))
   ;


      --  truncated natural square root, Von Neumann's algorithm
   function Sqrt_Von_Neumann64 (X : in Sqrt_Domain64) return Sqrt_Range64
     with Post => (Sqrt_Von_Neumann64'Result *
                     Sqrt_Von_Neumann64'Result) <= X and
     (if Sqrt_Von_Neumann64'Result < Sqrt_Range64'Last then
        (Sqrt_Von_Neumann64'Result + 1) *
          (Sqrt_Von_Neumann64'Result + 1) > X);
   -- We could put (for all y in Sqrt_Range'Range =>
   --                (if y > result then y ** 2 > x))

end P64;
