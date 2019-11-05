package body P is
   procedure Zero (Arg : out Integer) is
   begin
      Arg := 0;
   end Zero;
begin
   Zero (Q.X);
end P;
