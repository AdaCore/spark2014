procedure Loop_Exit3 is
   X : Integer := 1;
   Y : Boolean := False;
begin
   while X > 0 loop
      Y := False;
      while X > 0 loop
         if X > 0 then
            X := 0;
            Y := True;
            exit;
         end if;
         for I in 1 .. 3 loop
            null;
         end loop;
      end loop;
      pragma Assert (Y = False);  --  @ASSERT:FAIL
   end loop;
end Loop_Exit3;
