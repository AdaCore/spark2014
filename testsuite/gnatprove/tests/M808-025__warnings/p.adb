procedure P (Y : out Integer) is pragma SPARK_Mode (On);
   type M is mod 2*32;
   pragma Warnings (Off); -- no reason given
   Z1 : Natural := 0;
   pragma Warnings (On);
   pragma Warnings (Off, "*has no effect*", Reason => "unused Z2, but that's OK");
   Z2 : Natural := 0;
   pragma Warnings (On, "*has no effect*");
   pragma Warnings (Off, Reason => "unused Z3, but that's also OK");
   Z3 : Natural := 0;
   pragma Warnings (On);
   X : Natural := 0;
begin
   if X = 0 then
      Y := X;
   end if;
   Y := X;
   pragma Assert (X = 0);
end P;
