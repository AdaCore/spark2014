--  This proof was originally done by Claude Marché in Why3 and can be found
--  in the repository of Why3: examples/in_progres/isqrt_von_neumann

with Interfaces; use Interfaces;

package P32
  with SPARK_Mode => On
is
   subtype Sqrt_Domain32 is Integer range 0 .. 2**31 - 1;
   subtype Sqrt_Range32  is Integer range 0 .. 46340;

   use type Interfaces.Unsigned_32;
   subtype U32 is Interfaces.Unsigned_32;

   function Sqr (X : U32) return U32 is
     (X * X);

   procedure Lemma_Bv (X, Y : U32) with
     Ghost,
     Post => Sqr(X + Y) = Sqr(X) + Y * (2 * X + Y);

   --  truncated natural square root, Von Neumann's algorithm
   function Sqrt_Von_Neumann_Aux32 (X : in U32) return U32
     with Post => ((Sqrt_Von_Neumann_Aux32'Result *
                     Sqrt_Von_Neumann_Aux32'Result) <= X and
     --  In bitvectors, this postcondition is the correct one
                  (Sqrt_Von_Neumann_Aux32'Result + 1) *
                       (Sqrt_Von_Neumann_Aux32'Result + 1) - 1 >= X)
     and then
       (if X <= U32 (Sqrt_Domain32'Last) Then
              Sqrt_Von_Neumann_Aux32'Result <= U32 (Sqrt_Range32'Last))
   ;


      --  truncated natural square root, Von Neumann's algorithm
   function Sqrt_Von_Neumann32 (X : in Sqrt_Domain32) return Sqrt_Range32
     with Post => (Sqrt_Von_Neumann32'Result *
                     Sqrt_Von_Neumann32'Result) <= X and
     (if Sqrt_Von_Neumann32'Result < Sqrt_Range32'Last then
        (Sqrt_Von_Neumann32'Result + 1) *
          (Sqrt_Von_Neumann32'Result + 1) > X);
   -- We could put (for all y in Sqrt_Range'Range =>
   --                (if y > result then y ** 2 > x))

end P32;
