package T1Q1B
  with SPARK_Mode
is

   procedure Increment (X : in out Integer)
     with Pre => X < Integer'Last;

end T1Q1B;
