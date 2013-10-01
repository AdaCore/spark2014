package T1Q1B
is
   pragma SPARK_Mode;

   procedure Increment (X: in out Integer)
     with Pre => X < Integer'Last;

end T1Q1B;
