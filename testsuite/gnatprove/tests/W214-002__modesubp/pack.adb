package body Pack is

   Z : Integer;
   procedure Incr_Glob is
   begin
      Z := Z + 1;
   end Incr_Glob;

   procedure Incr (X : in out Integer) is
   begin
      X := X + 1;
   end Incr;

   procedure Incr_Full (X : in out Integer) is
   begin
      X := X + 1;
   end Incr_Full;
end Pack;
