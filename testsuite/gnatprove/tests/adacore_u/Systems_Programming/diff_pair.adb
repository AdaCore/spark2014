package body Diff_Pair
  with SPARK_Mode
is
   function Max return Integer is
      Val1 : constant Natural := X.U;
      Val2 : constant Natural := X.V;
   begin
      return Natural'Max (Val1, Val2);
   end Max;

   function Max2 return Integer is
      P    : constant Pair := X;
      Val1 : constant Natural := P.U;
      Val2 : constant Natural := P.V;
   begin
      return Natural'Max (Val1, Val2);
   end Max2;

end Diff_Pair;
