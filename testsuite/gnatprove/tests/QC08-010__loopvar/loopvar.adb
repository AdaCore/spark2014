procedure Loopvar with SPARK_Mode is
   X : Integer := 1;
begin
   while X < 10 loop
      pragma Loop_Variant (Increases => X);
      X := X + 1;
      pragma Assert (X > 0);
   end loop;
end Loopvar;
