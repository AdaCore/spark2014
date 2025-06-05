package Assert_Static_False
  with SPARK_Mode
is

   function Assert_False (N : Natural) return Natural;

   function Assert_False_Expr (N : Natural) return Natural;

   function Assert_False_Tautology (N : Natural) return Natural;

   function Assert_False_No_Solution (X, Y : Natural) return Natural
   with
     Pre =>
       (2 * X <= Natural'Last
        and then 3 * Y <= Natural'Last
        and then 2 * X + 3 * Y <= Natural'Last);

end Assert_Static_False;
