procedure Main with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);
   function Rand (X : Integer) return Integer with
     Import;
   function Id_Pre (X : Integer) return Integer is (X) with
     Pre => X <= Rand (0);
   type Nat_Array is array (Positive range <>) of Natural;

   A : Nat_Array (Id (1) .. Id (10)) := (others => 1);

   subtype My_Pos_1 is Natural range Id (1) .. Id (15);
   subtype My_Pos_2 is Natural range Id (1) .. Id (5);

begin
   if Rand (0) = 0 then
      A (2 .. 12) := (others => 2); -- @INDEX_CHECK:FAIL

   --  Checks that the slice is a valid slice

   elsif Rand (1) >= 1 then
      A (1 .. Rand (1)) (1) := 2; -- @INDEX_CHECK:FAIL

   --  RTE checks in the computation of the bounds

   elsif Rand (2) in 1 .. 10 then
      A (1 .. Id_Pre (Rand (2))) (1) := 2; -- @PRECONDITION:FAIL
   elsif Rand (3) in 1 .. 10 then
      A (Id_Pre (Rand (3)) .. 10) (10) := 2; -- @PRECONDITION:FAIL

   --  Checks on subtype range

   elsif Rand (4) in 1 .. 10 then
      A (My_Pos_1 range 1 .. Rand (4)) (1) := 2; -- @RANGE_CHECK:PASS
      A (My_Pos_2 range 1 .. Rand (4)) (1) := 2; -- @RANGE_CHECK:FAIL
   end if;
end Main;
