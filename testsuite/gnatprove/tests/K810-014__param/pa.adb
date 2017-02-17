package body Pa is

   function F return T is
      V : T := (D => 2, X => 123);
   begin
      return V;
   end F;

end Pa;
