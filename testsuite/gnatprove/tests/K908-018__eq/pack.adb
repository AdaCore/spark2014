package body Pack is

   function Equal (A, B : Ar) return Boolean is
   begin
      return A = B;
   end Equal;

   function Equal (A, B : Rec) return Boolean is
   begin
      return A = B;
   end Equal;

end Pack;
