package body Pack
  with SPARK_Mode => On
is
   function F return Boolean is
      B : access Boolean;
   begin
      B := new Boolean;
      B.all := True;
      return B.all;
   end F;

   procedure P is
      pragma SPARK_Mode (Off);
   begin
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
