procedure Crash_In_Loop with SPARK_Mode is
   X : Integer := 0;
   function Post_Incr return Integer
     with Side_Effects, Global => (In_Out => X);
   function Post_Incr return Integer is
      V : constant Integer := X;
   begin
      X := X + 1;
      return V;
   end Post_Incr;
begin
   loop
      declare
         Val : Integer;
      begin
         Val := Post_Incr;
         exit when Val = 42;
      end;
   end loop;
end Crash_In_Loop;
