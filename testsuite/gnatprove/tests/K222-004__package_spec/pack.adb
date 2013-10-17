package body Pack
   with SPARK_Mode
is
   function F return Boolean is
      pragma SPARK_Mode (Off);
      B : access Boolean;
   begin
      B := new Boolean;
      B.all := True;
      return B.all;
   end F;

   procedure P is

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
