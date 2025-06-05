package body Assert_Static_False with SPARK_Mode is

   function Assert_False (N : Natural) return Natural is
   begin
      pragma Assert (False);
      return N;
   end Assert_False;

   function Assert_False_Expr (N : Natural) return Natural is
   begin
      pragma Assert (2 /= 2);
      return N;
   end Assert_False_Expr;

   function Assert_False_Tautology (N : Natural) return Natural is
   begin
      pragma Assert (N /= N);
      return N;
   end Assert_False_Tautology;

   function Assert_False_No_Solution (X, Y : Natural) return Natural is
   begin
      pragma Assert (2 * X + 3 * Y = 7);
      return X;
   end Assert_False_No_Solution;

end Assert_Static_False;
