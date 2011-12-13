package body Pack is
   pragma Annotate (gnatprove, Force);

   function F return Boolean is
      pragma Annotate (gnatprove, Force);
      B : Boolean;
   begin
      B := True;
      return B;
   end F;

   procedure P is
      pragma Annotate (gnatprove, Force);
      B : Boolean;
   begin
      B := False;
      if B then
         null;
      end if;
   end P;
end;
