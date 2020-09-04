with Interfaces; use Interfaces;

package Bvext
with SPARK_Mode, Ghost
is

   function Nth (X : Unsigned_64; Pos : Natural) return Boolean 
   is ((Shift_Right (X, Pos) and 1) = 1);
   pragma Annotate (GNATprove, Inline_For_Proof, Nth);

   function Nth (X : Unsigned_8; Pos : Natural) return Boolean
   is ((Shift_Right (X, Pos) and 1) = 1);
   pragma Annotate (GNATprove, Inline_For_Proof, Nth);

   function Nth_Bv (X, Pos : Unsigned_64) return Boolean
   is ((Shift_Right (X, Natural (Pos)) and 1) = 1)
   with Pre => Pos <= 64;
   pragma Annotate (GNATprove, Inline_For_Proof, Nth_Bv);

   function Nth_Bv (X, Pos : Unsigned_8) return Boolean
   is ((Shift_Right (X, Natural (Pos)) and 1) = 1);
   pragma Annotate (GNATprove, Inline_For_Proof, Nth_Bv);

   function Extract_Seq (X : Unsigned_64; I, N : Natural) return Unsigned_64
   is (if I > N then 0 else (Shift_Right (X, 64 - (I + N)) and (2 ** N - 1)))
   with Pre => (I in 0 .. 63 and then N in 1 .. 64 - I);

   function Eq_Sub (X, Y : Unsigned_64; I, N : Natural) return Boolean
   is (Extract_Seq (X, I, N) = Extract_Seq (Y, I, N))
   with Pre => (I in 0 .. 63 and then N in 1 .. 64 - I);

   function Eq_Sub_Bv (X, Y, I, N : Unsigned_64) return Boolean
   is (Extract_Seq (X, Natural (I), Natural (N)) = Extract_Seq (Y, Natural (I), Natural (N)))
   with Pre => (I in 0 .. 63 and then N in 1 .. 64 - I);

end Bvext;
