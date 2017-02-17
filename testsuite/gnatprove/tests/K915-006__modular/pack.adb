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

   function Minus (A, B : Modular) return Modular
   is
   begin
      return A - B;
   end Minus;

   function Test_Div (A, B : Modular) return Modular
   is
   begin
      return (A + B) / (Subst (A,B)); -- OK
   end Test_Div;
end Pack;
