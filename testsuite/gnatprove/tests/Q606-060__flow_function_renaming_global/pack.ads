package Pack with SPARK_Mode is
   X : Integer := 0;

   function Get_Integer return Integer with Global => X;
end Pack;
