with Test_External_Variables; use Test_External_Variables;

procedure Test_Volatile_Loop_Param
  with SPARK_Mode
is
begin
   --  A constant, a discriminant or a loop parameter shall not be Volatile

   for Intex in Volatile_Int'Range loop
      null;
   end loop;
end;
