package body Account3 with
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
         declare
            Tmp : constant Natural := Num_Accounts;
         begin
            Num_Accounts := Tmp + 1;
         end;
      end loop;
   end Account_Management;

end Account3;
