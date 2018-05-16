package body Pkg1 with SPARK_Mode => Off is

   function F (X : Integer) return Integer;

   function F (X : Integer) return Integer is
   begin
      return X / 2;
   end F;

   X : constant Boolean := (for all X in Integer => F (X) = X);

   function P return Boolean is begin
      return X;
   end P;

end Pkg1;
