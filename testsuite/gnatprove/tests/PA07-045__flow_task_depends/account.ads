package Account is

   Num_Accounts : Natural := 0;

   task type Account_Management with
     Global  => (In_Out       => Num_Accounts),
     Depends => (Num_Accounts => Num_Accounts);

end Account;
