with SPARK.Big_Integers; use SPARK.Big_Integers;

package Recursive_Subprograms with SPARK_Mode is

   function Fibonacci (N : Big_Natural) return Big_Natural is
     (if N = 0 then 0
      elsif N = 1 then 1
      else Fibonacci (N - 1) + Fibonacci (N - 2))
   with Subprogram_Variant => (Decreases => N);
end Recursive_Subprograms;
