procedure Main3 with SPARK_Mode is
   procedure Exp (N : Integer) is
   begin
      pragma Assert ((3 ** (N + 1)) / (3 ** N) = 3);
   end;
begin
   Exp (666);
end;
