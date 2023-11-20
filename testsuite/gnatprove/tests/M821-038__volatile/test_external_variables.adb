package body Test_External_Variables is
   pragma SPARK_Mode (On);

   procedure Error_Proc_1 is begin null; end Error_Proc_1;
   procedure OK_Proc_1    is begin null; end OK_Proc_1;
   procedure OK_Proc_2    is begin null; end OK_Proc_2;

begin
   --  A constant, a discriminant or a loop parameter shall not be Volatile

   for Intex in Volatile_Int'Range loop
      null;
   end loop;
end Test_External_Variables;
