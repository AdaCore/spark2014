procedure Full
   (A, B : Integer;
    Y1, Y2, Y3, Y4, Y5 : out Natural;
    Z1, Z2, Z3 : out Boolean)
  with SPARK_Mode,
       Depends => (Y1 => (A,B),
                   Y2 => (A,B),
                   Y3 => (A,B),
                   Y4 => (A,B),
                   Y5 => null,
                   Z1 => null,
                   Z2 => null,
                   Z3 => null)
is
   type A2D is array (Positive range <>, Positive range <>) of Integer;
   type T (L, H : Integer) is record
      A : String (L .. H);
      C : A2D (1 .. 1, L .. H);
   end record;
   X : T (A, B);
   subtype S is T (A, B);
   subtype Scal is Integer range A .. B;
begin
   Y1 := X.A'Size;   --  depends on A and B
   Y2 := X.C'Size;   --  depends on A and B
   Y3 := X'Size;     --  depends on A and B
   Y4 := S'Size;     --  depends on A and B
   Y5 := Scal'Size;  --  depends on Integer'Range, so not on A and B

   --  The following 'Size attributes return very large, non-static
   --  values, so we compare them with 0, so they can be examined in
   --  the Depends contract.
   Z1 := T'Size /= 0;
   Z2 := String'Size /= 0;
   Z3 := A2D'Size /= 0;
end;
