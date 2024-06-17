procedure Test_Loop with SPARK_Mode is
   function F return Integer with
     Import,
     Global => null,
     Always_Terminates,
     Side_Effects,
     Exceptional_Cases => (Program_Error => True);
   X : Integer := 1;
   Y : Integer := 1;
begin
   while Y <= 42 loop
      declare
         Local : Integer;
      begin
         X := X + 1;
         Local := F;
         Y := Y + Local;
         exit;
      exception
         when Program_Error =>
            Y := Y + 1;
      end;
   end loop;
   pragma Assert (X = 2); --@ASSERT:FAIL

end Test_Loop;
