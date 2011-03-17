package body Pack is
   pragma Annotate (Formal_Proof, On);
      
   function F return Boolean is
      B : access Boolean;
   begin
      B := new Boolean;
      B.all := True;
      return B.all;
   end F;

   procedure P is
   begin
      pragma Annotate (Formal_Proof, Off);
      declare
         B : access Boolean;
      begin
         B := new Boolean;
         B.all := True;
         if B.all then
            return;
         end if;
      end;
   end P;
end;
