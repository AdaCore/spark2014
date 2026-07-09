package body Zero_And_Edge_Cases
  with SPARK_Mode
is

   function Any_Power_Zero_Is_One (X : Integer) return Boolean is
   begin
      return X ** 0 = 1;
   end Any_Power_Zero_Is_One;

   function Zero_To_Positive_Power_Is_Zero (N : Positive) return Boolean is
   begin
      return 0 ** N = 0;
   end Zero_To_Positive_Power_Is_Zero;

   function One_To_Any_Power_Is_One (N : Natural) return Boolean is
   begin
      return 1 ** N = 1;
   end One_To_Any_Power_Is_One;

   function Minus_One_Alternates (N : Natural) return Boolean is
   begin
      return (if N mod 2 = 0 then (-1) ** N = 1 else (-1) ** N = -1);
   end Minus_One_Alternates;

end Zero_And_Edge_Cases;
