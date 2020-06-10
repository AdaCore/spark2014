procedure Test_Aggr with SPARK_Mode is
   type Matrice is array (Positive range <>, Positive range <>) of Natural;

   X : Positive := 10;
   Y : Positive := 10;

   procedure Test with Global => (Input => (X, Y)) is
      C : constant positive := X;
      subtype SC is Positive range C .. 5;
      D : constant positive := Y;
      subtype SD is Positive range C .. 5;
      ZC : Matrice := (1 .. 5 => (SC range 1 .. 5 => 1)); --@RANGE_CHECK:FAIL
      ZD : Matrice (1 .. 2, 1 .. 5) := ((1 .. 5 => 2), (SD range 1 .. 5 => 1)); --@RANGE_CHECK:FAIL
   begin
      null;
   end Test;
begin
   null;
end Test_Aggr;
