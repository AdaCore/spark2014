package body P is
   procedure Incr (X : in out Integer) is
   begin
      X := X + 1; --@OVERFLOW_CHECK:FAIL
   end Incr;
end P;
