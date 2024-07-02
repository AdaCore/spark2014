procedure Foo (X : Float) with SPARK_Mode is
   Y : Float := X;
begin
   if Y < 0.0 then
      Y := -X;
   end if;
   pragma Assert (Float'Copy_Sign (1.0, Y) = Float'Copy_Sign (1.0, abs X)); --@ASSERT:FAIL
end Foo;
