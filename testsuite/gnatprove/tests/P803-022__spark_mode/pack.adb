package body Pack is

   type T is access Integer;
   X : T;
   pragma Assert (X = null);

   procedure P (X : in out Integer) with SPARK_Mode is
   begin
      X := X + 1;
   end P;

end Pack;
