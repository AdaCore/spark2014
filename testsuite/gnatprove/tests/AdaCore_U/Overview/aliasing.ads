package Aliasing
  with SPARK_Mode => On
is
  procedure Permute (X, Y, Z : in out Positive);

  procedure Swap (X, Y : in out Positive);

  type Rec is record
    F1 : Positive;
    F2 : Positive;
  end record;

  procedure Swap_Fields (R : in out Rec);

  type P_Array is array (Natural range <>) of Positive;

  procedure Swap_Indexes (A : in out P_Array; I, J : Natural);

end Aliasing;
