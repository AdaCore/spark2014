package Power_and_Sum is pragma SPARK_Mode (On);
   procedure Power(X : in Integer; N : in Positive; Result: out Integer) with
     Post => X ** N = Result;

   procedure Sum(N : in Positive; Result: out Positive) with
     Post => 2 * Result = N * (N+1)
   ;
   procedure Sum_Of_Sum(N : in Positive; Result: out Positive) with
     Post => 6 * Result = N * (N+1) * (N+2)
   ;

end Power_and_Sum;
