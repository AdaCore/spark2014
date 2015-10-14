pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Account with SPARK_Mode is
   Num_Accounts : Natural := 0;

   type Account_Number is new Integer;
   procedure Get_Next_Account_Created;

   task type Account_Management with
     Global => (In_Out => Account.Num_Accounts),
     Depends => (Account.Num_Accounts => Account.Num_Accounts,
                 Account_Management => Account_Management);
end Account;
