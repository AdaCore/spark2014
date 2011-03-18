package body Pack is
   pragma Annotate (Formal_Proof, On);

   function F return Boolean is
      pragma Annotate (Formal_Proof, On);
      B : Boolean;
   begin
      B := True;
      return B;
   end F;

   procedure P is
      pragma Annotate (Formal_Proof, On);
      B : Boolean;
   begin
      B := False;
      if B then
         null;
      end if;
   end P;
end;
