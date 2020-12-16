pragma SPARK_Mode;
procedure Prog (X : in out Integer) with Pre => X < Integer'Last is
begin
   X := X + 1;
end Prog;
  
