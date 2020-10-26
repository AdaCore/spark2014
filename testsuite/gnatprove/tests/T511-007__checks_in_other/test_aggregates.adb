procedure Test_Aggregates with SPARK_Mode is
   type Int_Array is array (Positive range <>) of Integer;

   function F (X : Integer) return Integer is (X);
   function Only_6 (X : Integer) return Integer is (X) with
     Pre => X = 6;

   X : Int_Array := (1 | 5 => F (0), 2 .. 4 => F (1));
   V : Int_Array := (X with delta 2 .. 4 => 2, F (3) => 3);

   U : Int_Array (1 .. F (6)) :=
     (declare
      C : constant Integer := F (1);
      begin
        (for I in 1 | 5  => V (I),
         for I in 2 .. 4 => I + C,
         for I in others => Only_6 (I)));
begin
   pragma Assert (U = (0, 3, 4, 5, 0, 6));
end Test_Aggregates;
