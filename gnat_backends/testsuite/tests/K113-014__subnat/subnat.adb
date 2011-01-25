package body Subnat is
   function F (X : Natural) return Integer
   is
   begin
      return X;
   end F;

   function G (X : Integer) return Positive
   is
   begin
      return X;
   end G;
end Subnat;
