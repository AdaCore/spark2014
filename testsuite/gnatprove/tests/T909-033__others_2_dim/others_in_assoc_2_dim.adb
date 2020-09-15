procedure Others_In_Assoc_2_Dim with SPARK_Mode is
   type Matrix is array (Positive range <>, Positive range <>) of Integer;
   function Id (X : Integer) return Integer is (X);
   function No (X : Integer) return Integer is (X) with
     Pre => False;

   B : constant Matrix (1 .. 0, 2 .. 4) := (for I in others => (Positive range Id (0) .. Id (5) => No (I))); --@RANGE_CHECK:FAIL
begin
   null;
end Others_In_Assoc_2_Dim;
