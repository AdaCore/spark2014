package Account3 with
  SPARK_Mode
is
   Num_Accounts : Natural := 0 with Atomic;

   task type Account_Management with
     Global  => (In_Out => Num_Accounts),
     Depends => (Account_Management => Account_Management,
                 Num_Accounts => Num_Accounts);
end Account3;
