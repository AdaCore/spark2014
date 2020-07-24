package Account2 with
  SPARK_Mode
is
   Num_Accounts : Natural := 0 with Atomic;

   task type Account_Management;
end Account2;
