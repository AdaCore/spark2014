procedure Iterated_Aggregates with SPARK_Mode is
   type Matrix is array (Positive range <>, Positive range <>) of Integer;

   --  A positional outer dimension containing an iterated association
   A : constant Matrix := ((for J in 1 .. 3 => J), (for J in 1 .. 3 => J + 3));

   --  A singleton positional outer dimension
   B : constant Matrix := [[for J in 1 .. 3 => J]];

   --  Mix an iterated association and an others choice
   C : constant Matrix (1 .. 3, 1 .. 3) :=
     (1 => (for J in 1 .. 3 => (declare V : constant Integer := J; begin V)),
      others => (others => 0));

   E : constant Matrix (1 .. 3, 1 .. 3) :=
     (for I in 1 .. 3 => (1 => I, 2 => I + 1, others => 0));

   type Vector is array (Positive range <>) of Integer;
   V : constant Vector := (1, 2, 3);
   D : constant Vector := (V with delta for J in 1 .. 2 => J + 10);
begin
   pragma Assert (A (2, 3) = 6);
   pragma Assert (B (1, 3) = 3);
   pragma Assert (C (1, 3) = 3 and C (3, 3) = 0);
   pragma Assert (E (3, 1) = 3 and E (3, 2) = 4 and E (3, 3) = 0);
   pragma Assert (D (1) = 11 and D (2) = 12 and D (3) = V (3));
end Iterated_Aggregates;
