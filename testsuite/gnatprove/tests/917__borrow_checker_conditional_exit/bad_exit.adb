procedure Bad_Exit with SPARK_Mode is
   type AInt is access Integer;
   X : AInt := new Integer'(0);
   Y : AInt := null;
   function Random return Boolean with Import, Global => null;
   procedure Swap (X, Y : AInt) with Import, Global => null, Always_Terminates => True;
begin
   loop
      Y := X;
      exit when Random;
      Swap (X, Y);
   end loop;
end Bad_Exit;
