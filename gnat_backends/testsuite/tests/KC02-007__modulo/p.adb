package body P is

   function F (X : T) return Integer is
      Y : T := X + 2;
   begin
      return Integer(Y);
   end F;

   function G (X : T) return Integer is
      Y : T := X + 2;
   begin
      return Integer(Y);
   end G;

   function M return Integer is
   begin
      return T'Modulus;
   end M;

   function Id (X : T) return T is
   begin
      return T'Mod (X);
   end Id;

end P;
