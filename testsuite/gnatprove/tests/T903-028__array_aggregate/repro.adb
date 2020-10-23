procedure Repro
   with SPARK_Mode => On
is
   function Id (X : Positive) return Positive is (X);
   type Nat_Array is array (Positive range <>) of Integer;
   subtype S is Nat_Array (1 .. Id (7));
   A : S := (8 => 15, others => 0); --@RANGE_CHECK:FAIL
begin
   null;
end Repro;
