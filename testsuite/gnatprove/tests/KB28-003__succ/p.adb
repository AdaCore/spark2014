package body P is

   function Id_Not_A (X : T) return T
   is
   begin
      return T'Succ (T'Pred (X));
   end Id_Not_A;

   function Id_Not_D (X : T) return T
   is
   begin
      return T'Pred (T'Succ (X));
   end Id_Not_D;

   function Id_Gen (X : T) return T
   is
   begin
      return T'Val (T'Pos (X));
   end Id_Gen;
end P;
