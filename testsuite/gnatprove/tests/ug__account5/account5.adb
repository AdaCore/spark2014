package body Account5 with
  SPARK_Mode
is
   protected body Protected_Natural is
      procedure Incr is
      begin
         The_Data := The_Data + 1;
      end Incr;

      function Get return Natural is (The_Data);
   end Protected_Natural;

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
            X : constant Natural := Num_Accounts.Get;
         begin
            if X < Max_Accounts then
               Num_Accounts.Incr;
            end if;
         end;
      end loop;
   end Account_Management;

end Account5;
