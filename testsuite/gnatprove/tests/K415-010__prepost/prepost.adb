package body Prepost is

   function F (Z : Integer) return Boolean is
   begin
      pragma Assert (Z = 0);
      return True;
   end F;

   function Fun_Is_Zero (X : Integer) return Boolean is
   begin
      return Is_Zero (X);
   end Fun_Is_Zero;

   function G (Z : Integer) return Boolean is
   begin
      pragma Assert (Z = 0);
      return True;
   end G;

end Prepost;
