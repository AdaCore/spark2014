procedure Full
   (A, B : Integer;
    Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8 : out Natural)
  with SPARK_Mode,
       Depends => (Y1 => (A,B),
                   Y2 => (A,B),
                   Y3 => (A,B),
                   Y4 => (A,B),
                   Y5 => null,
                   Y6 => null,
                   Y7 => null,
                   Y8 => null)
is
   type A2D is array (Positive range <>, Positive range <>) of Integer;
   type T (L, H : Integer) is record
      A : String (L .. H);
      C : A2D (1 .. 1, L .. H);
   end record;
   X : T (A, B);
   subtype S is T (A, B);
   subtype Scal is Integer range A .. B;
   Unsupported : constant Integer := (if A = B then 1 else 0);
   --  A dummy value to handle Object'Alignment, which is currently rejected
   --  in marking.
begin
   Y1 := Unsupported; --X.A'Alignment;   --  depends on A and B
   Y2 := Unsupported; --X.C'Alignment;   --  depends on A and B
   Y3 := Unsupported; --X'Alignment;     --  depends on A and B
   Y4 := S'Alignment;     --  depends on A and B
   Y5 := Scal'Alignment;  --  depends on Integer'Range, so not on A and B
   Y6 := T'Alignment;
   Y7 := String'Alignment;
   Y8 := A2D'Alignment;
end;
