package body Pack is 

   Value : Child;

   procedure Proc (P: in out Child) is
   begin
      P := Value;
   end Proc;

end Pack;
