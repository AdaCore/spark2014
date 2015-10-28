package body Account7 with
  SPARK_Mode
is
   protected body Protected_Natural is
      entry Incr when Not_Full is
      begin
         The_Data := The_Data + 1;
         if The_Data = Max_Accounts then
            Not_Full := False;
         end if;
      end Incr;

      function Get return Natural is (The_Data);
   end Protected_Natural;

   procedure Get_Next_Account_Created is
   begin
      --  wait for external interaction here...
      null;
   end Get_Next_Account_Created;

   procedure Incr_Num_Accounts is
   begin
      Num_Accounts.Incr;
   end Incr_Num_Accounts;

   protected body Bad is
      entry Bad_E when True is
      begin
         Incr_Num_Accounts;
      end Bad_E;

      procedure Bad_P is
      begin
         Incr_Num_Accounts;
      end Bad_P;

      function Bad_F return Natural is
      begin
         Incr_Num_Accounts;
         return Num_Accounts.Get;
      end Bad_F;
   end Bad;

   task body Account_Management is
   begin
      loop
         Get_Next_Account_Created;
         Num_Accounts.Incr;
      end loop;
   end Account_Management;

end Account7;
