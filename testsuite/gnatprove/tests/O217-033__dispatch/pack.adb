package body Pack is

   procedure Incr (O : in out Root) is
   begin
      O.F1 := O.F1 + 1;
   end Incr;

   procedure Incr2 (O : in out Root) is
   begin
      Incr (O);
   end Incr2;

   procedure Incr2 (O : in out Child) is
   begin
      O.F2 := O.F2 + 1;
      Incr (O);
   end Incr2;

end Pack;
