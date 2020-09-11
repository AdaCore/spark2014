procedure D (I : Positive) with
  SPARK_Mode,
  Pre => I in 5 .. 10
is
   type A is array (Integer range 1 .. 10) of Integer;
   subtype Small_Int is Integer range 1 .. I;

   function Rand (X : Integer) return Integer with
     Import,
     Post => Rand'Result in 1 .. 10;

   X : A := (others => 0);
   Y : A := (X with delta Integer range 1 .. 2 => 3);
   Z : A := X'Update (Integer range 1 .. 2 => 3);
   Y1 : A := (X with delta Small_Int range 1 .. 2 => 3);
   Z1 : A := X'Update (Small_Int range 1 .. 2 => 3);
   Y2 : A := (X with delta Small_Int range 1 .. Rand (0) => 3); --@RANGE_CHECK:FAIL
   Z2 : A := X'Update (Small_Int range 1 .. Rand (1) => 3); --@RANGE_CHECK:FAIL
begin
   null;
end;
