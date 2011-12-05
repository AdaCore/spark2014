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

end P;
