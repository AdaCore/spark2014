package body Account8 with
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

   task body Account_Management is
   begin
      loop
         Get_Next_Account_Created;
         Num_Accounts.Incr;
      end loop;
   end Account_Management;

end Account8;
