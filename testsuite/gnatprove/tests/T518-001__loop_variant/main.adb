procedure Main with SPARK_Mode is
   X : Integer := 0;
   Y : Integer := 10;
begin
   while X < Integer'Last and Y > Integer'First loop
      pragma Loop_Variant
         (Increases => X,
          Decreases => Y,
          Decreases => 10 / Y);  --@DIVISION_CHECK:FAIL
      Y := Y - 1;
   end loop;

end Main;
