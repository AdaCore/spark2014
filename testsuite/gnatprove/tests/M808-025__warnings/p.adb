procedure P (Y : out Integer) is pragma SPARK_Mode (On);
   type M is mod 2*32;
   pragma Warnings (Off);
   Z1 : Natural := 0;
   pragma Warnings (On);
   pragma Warnings (Off, "*has no effect*");
   Z2 : Natural := 0;
   pragma Warnings (On, "*has no effect*");
   pragma Unreferenced (Z2);
   X : Natural := 0;
begin
   if X = 0 then
      Y := X;
   end if;
   Y := X;
   pragma Assert (X = 0);
end P;
