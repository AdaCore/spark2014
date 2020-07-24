package body Account1 with
  SPARK_Mode
is

   procedure Get_Next_Account_Created is
   begin
      --  wait for external interaction here...
      null;
   end Get_Next_Account_Created;

   task body Account_Management is
   begin
      loop
         Get_Next_Account_Created;
         Num_Accounts := Num_Accounts + 1;
      end loop;
   end Account_Management;

end Account1;
