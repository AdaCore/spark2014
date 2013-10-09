package body X is
   pragma SPARK_Mode (Off);
   procedure P (x : T) is
   begin
      x.A.all := 0;
   end P;
end X;
