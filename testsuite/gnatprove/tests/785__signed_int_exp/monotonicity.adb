package body Monotonicity
  with SPARK_Mode
is

   function Strictly_Increasing_In_Exponent
     (X : Integer; N1, N2 : Small_Exp) return Boolean is
   begin
      return X ** N1 < X ** N2;
   end Strictly_Increasing_In_Exponent;

   function Nondecreasing_In_Exponent
     (X : Integer; N1, N2 : Small_Exp) return Boolean is
   begin
      return X ** N1 <= X ** N2;
   end Nondecreasing_In_Exponent;

   function Nondecreasing_In_Base
     (X1, X2 : Small_Base; N : Positive) return Boolean is
   begin
      return X1 ** N <= X2 ** N;
   end Nondecreasing_In_Base;

end Monotonicity;
