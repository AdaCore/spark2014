procedure P (Y : out Integer) is pragma SPARK_Mode (On); 
   type M is mod 2*32;
   pragma Warnings (Off);
   Z : Natural := 0;   
   pragma Warnings (On);   
   X : Natural := 0;
begin
   if X = 0 then
      Y := X;
   end if;
   Y := X;
   pragma Assert (X = 0);
end P;
