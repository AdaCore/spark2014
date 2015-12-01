package Aliasing
  with SPARK_Mode => On
is
  procedure Swap (X, Y : in out Positive);

  type P_Array is array (Natural range <>) of Positive;

  procedure Swap_Indexes (A : in out P_Array; I, J : Natural);

end Aliasing;
