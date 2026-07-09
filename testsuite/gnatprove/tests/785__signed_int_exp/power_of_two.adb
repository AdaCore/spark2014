package body Power_Of_Two
  with SPARK_Mode
is

   function Two_Pow (N : Exp_Range) return Positive is
   begin
      return 2 ** N;
   end Two_Pow;

   function Two_Pow_Is_Positive (N : Exp_Range) return Boolean is
   begin
      return 2 ** N > 0;
   end Two_Pow_Is_Positive;

   function Two_Pow_Even_For_Positive_N (N : Exp_Range) return Boolean is
   begin
      return 2 ** N mod 2 = 0;
   end Two_Pow_Even_For_Positive_N;

   function Two_Pow_Doubling (N : Natural) return Boolean is
   begin
      return 2 ** (N + 1) = 2 * 2 ** N;
   end Two_Pow_Doubling;

   function Two_Pow_Product (A, B : Natural) return Boolean is
   begin
      return 2 ** A * 2 ** B = 2 ** (A + B);
   end Two_Pow_Product;

   function Two_Pow_Strictly_Increasing (N1, N2 : Exp_Range) return Boolean is
   begin
      return 2 ** N1 < 2 ** N2;
   end Two_Pow_Strictly_Increasing;

   function Range_Bound_Constants return Boolean is
      Max_32 : constant Integer := 2 ** 31 - 1;
      Min_32 : constant Integer := -(2 ** 31);
      Max_64 : constant Long_Long_Integer := 2 ** 63 - 1;
      Min_64 : constant Long_Long_Integer := -(2 ** 63);
   begin
      return
        Max_32 > 0 and then Min_32 < 0 and then Max_64 > 0 and then Min_64 < 0;
   end Range_Bound_Constants;

end Power_Of_Two;
