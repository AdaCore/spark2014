package body Fixed_Exponent
  with SPARK_Mode
is

   function Square (X : Small) return Integer is
   begin
      return X ** 2;
   end Square;

   function Cube (X : Small) return Integer is
   begin
      return X ** 3;
   end Cube;

   function Fourth_Power (X : Bounded_For_Fourth) return Integer is
   begin
      return X ** 4;
   end Fourth_Power;

   function Fifth_Power (X : Bounded_For_Fifth) return Integer is
   begin
      return X ** 5;
   end Fifth_Power;

end Fixed_Exponent;
