package body Account is

   task body Account_Management is
   begin
      loop
         Num_Accounts := Num_Accounts + 1;
      end loop;
   end Account_Management;

end Account;
