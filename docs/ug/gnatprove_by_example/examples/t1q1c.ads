pragma SPARK_Mode;

package T1Q1C
is

  procedure Increment (X: in out Integer)
    with Pre => X < Integer'Last;

end T1Q1C;
