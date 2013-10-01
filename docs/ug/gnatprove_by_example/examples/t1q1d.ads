pragma SPARK_Mode;

package T1Q1D
is

  procedure Increment (X: in out Integer)
    with Pre => X < Integer'Last;

  procedure Add2 (X : in out Integer)
    with Pre => X <= Integer'Last - 2,
         Post => X = X'Old + 2;

end T1Q1D;
