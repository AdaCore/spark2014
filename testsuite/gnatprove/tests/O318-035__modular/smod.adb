procedure Smod with
  SPARK_Mode
is
   procedure Test (X, Y : Integer) with
     Pre => X = 0 and Y = 255
   is
      type M is mod 2**8;
      subtype S is M range M(X) .. M(Y);
      V : Integer := -3;
      W : S;
   begin
      W := S(V);  --  @RANGE_CHECK:FAIL
   end Test;
begin
   Test (0, 255);
end Smod;
