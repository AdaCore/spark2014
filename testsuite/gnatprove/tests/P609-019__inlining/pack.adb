package body Pack with
  SPARK_Mode
is
   procedure Q (X : in out Integer) is
   begin
      X := X + 1;
      return;
   end Q;

   procedure P (X : in out Integer) is
   begin
      Q (X);
   end P;

end Pack;
