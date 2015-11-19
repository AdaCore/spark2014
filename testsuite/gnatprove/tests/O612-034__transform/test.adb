package body Test is

   procedure P (X : Integer) is
   begin
      pragma Assert (1 <= X and then X <= 12);
   end P;

end Test;
