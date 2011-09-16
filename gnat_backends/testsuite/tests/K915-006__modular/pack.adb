package body Pack is

   function Next (M : Modular) return Modular is
   begin
      return M + 1;
   end Next;

   function Next1 (M : Modular) return Modular is
   begin
      return M + 1;
   end Next1;

   function Next255 (M : Modular) return Modular is
   begin
      return M + 1;
   end Next255;

end Pack;
