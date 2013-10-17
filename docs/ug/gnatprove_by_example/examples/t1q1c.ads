package T1Q1C
is
   pragma SPARK_Mode;

   procedure Increment (X: in out Integer)
     with Pre => X < Integer'Last;

end T1Q1C;
