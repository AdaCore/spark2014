with Interfaces; use Interfaces;

package Bvext
with SPARK_Mode, Ghost
is
   pragma Annotate (GNATprove, External_Axiomatization);

   function Nth (X : Unsigned_64; Pos : Natural) return Boolean with Import;
   function Nth (X : Unsigned_8; Pos : Natural) return Boolean with Import;

   function Nth_Bv (X, Pos : Unsigned_64) return Boolean with Import;
   function Nth_Bv (X, Pos : Unsigned_8) return Boolean with Import;

   function Eq_Sub (X, Y : Unsigned_64; I, N : Natural) return Boolean with Import;
   function Eq_Sub_Bv (X, Y, I, N : Unsigned_64) return Boolean with Import;

   function Eq (X, Y : Unsigned_64) return Boolean with Import;
end Bvext;
