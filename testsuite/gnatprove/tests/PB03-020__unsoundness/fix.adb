procedure Fix with SPARK_Mode is
   type F is delta 0.25 range -4000.0 .. 4000.0;

   X : F := 1.25;
   Y : F := 0.75;
   Z : F := X / Y;
begin
   pragma Assert (Z = 1.5); --@ASSERT:FAIL
end Fix;
