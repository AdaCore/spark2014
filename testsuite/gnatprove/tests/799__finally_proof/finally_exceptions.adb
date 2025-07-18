--  Exceptions must not cross finally boundaries in SPARK

procedure Finally_Exceptions with SPARK_Mode is
   E : exception;
   function Random return Integer with Import;
   X : Integer := Random;
begin
   begin
     if X = 0 then
       raise E;
     end if;
   finally
      if X /= 1 then
         raise E; --@RAISE:FAIL
      end if;
   end;
exception
   when others =>
      pragma Assert (X = 0); --@ASSERT:PASS
end Finally_Exceptions;
