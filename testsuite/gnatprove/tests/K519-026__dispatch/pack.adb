package body Pack is
   pragma SPARK_Mode (Off);

   Value : Child;

   procedure Proc (P: in out Child) is
   begin
      P := Value;
   end Proc;

end Pack;
