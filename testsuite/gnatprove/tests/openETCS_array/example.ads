package Example is pragma SPARK_Mode (On);
   function Saturated_Sum(X1, X2, Maximum : Natural) return Natural
   with
     Pre => ((X1 <= Natural'Last / 2) and (X2 <= Natural'Last / 2)),
     Post => (if X1 + X2 <= Maximum then saturated_sum'Result = X1 + X2
              else saturated_sum'Result = Maximum);
end;
