package Account4 with
  SPARK_Mode
is
   Num_Accounts : Natural := 0 with Atomic;
   Max_Accounts : constant Natural := 100;

   task type Account_Management;
end Account4;
