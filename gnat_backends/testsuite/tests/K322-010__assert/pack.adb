package body Pack is

   function F return Boolean is
      pragma Assert (X > 0);
   begin
      pragma Assert (X = 10);
      pragma Annotate (Formal_Proof, On);
      return True;
   end F;

   pragma Assert (X > 0);

   procedure P is
      pragma Assert (X > 0);
   begin
      pragma Assert (X = 10);
      null;
   end P;
end;
