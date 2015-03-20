package body Full
   with SPARK_Mode
is

   function Id (X : Integer) return Integer is (X);

   function Bump (X : Integer) return Integer
   is begin
      return X + 1;
   end Bump;

   procedure Use_Bump is
   begin
      Z := Bump (Z);
   end Use_Bump;

end Full;
