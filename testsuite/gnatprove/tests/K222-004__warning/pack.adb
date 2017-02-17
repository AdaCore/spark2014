package body Pack is


   function F return Boolean is

      B : Boolean;
   begin
      B := True;
      return B;
   end F;

   procedure P is

      B : Boolean;
   begin
      B := False;
      if B then
         null;
      end if;
   end P;
end;
