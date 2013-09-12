package body Dynamic is 

   function P (X : Positive) return Integer is
      Z : constant Integer := X + 1;
      M : Integer := X + 2;
      subtype A is Positive range 1 .. X;
      subtype B is Positive range 2 .. Z;
      subtype C is Positive range 3 .. M;
      subtype E is Positive range X .. 10;
      subtype F is Positive range Z .. 10;
      subtype G is Positive range M .. 10;
      subtype H is Positive range Z + 1 .. M - 1;

      type T is new Positive range X .. 10;

      OA : A := 1;
      OB : B := 2;
      OC : C := M;
      OE : E := X;
      OF_O : F := 10;
      OG : G := 10;
      OH : H := Z + 1;
   begin
      M := M + 1;
      return OG;
   end P;
end Dynamic;
