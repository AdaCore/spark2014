procedure Array_Conv (C : Positive) with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Integer;
   subtype S1 is Nat_Array (1 .. C);
   subtype S2 is S1;
   type Nat_Array_Array_1 is array (Positive range <>) of S1;
   type Nat_Array_Array_2 is array (Positive range <>) of S2;

   X : Nat_Array_Array_1 (1 .. 100) := (others => (others => 0));
   Y : Nat_Array_Array_2 (101 .. 200) := Nat_Array_Array_2 (X);
   pragma Assert (Y = (1 .. 100 => (others => 0)));
begin
   null;
end Array_Conv;
