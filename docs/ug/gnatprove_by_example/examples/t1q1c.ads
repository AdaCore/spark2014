package T1Q1C
  with SPARK_Mode
is

   procedure Increment (X : in out Integer)
     with Pre => X < Integer'Last;

   procedure Add2 (X : in out Integer);

end T1Q1C;
