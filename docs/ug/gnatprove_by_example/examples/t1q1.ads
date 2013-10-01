package T1Q1
is
   pragma SPARK_Mode;

  procedure Increment (X: in out Integer)
    with Pre => X < Integer'Last,
         Post => X = X'Old + 1;

end T1Q1;
