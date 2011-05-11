package body Sub is
   function F return Boolean is
      pragma Annotate (gnatprove, Force);
      B : access Boolean;
   begin
      B := new Boolean;
      B.all := True;
      return B.all;
   end F;

   procedure P is
   begin
      pragma Annotate (gnatprove, Force);
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
