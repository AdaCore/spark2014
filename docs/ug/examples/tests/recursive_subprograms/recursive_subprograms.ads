package Recursive_Subprograms with SPARK_Mode is
   type Nat is new Natural;
   function "+" (X, Y : Nat) return Nat is
     (if X > Nat'Last - Y then Nat'Last else X + Y);

   function Fibonacci (N : Nat) return Nat is
     (if N = 0 then 0
      elsif N = 1 then 1
      else Fibonacci (N - 1) + Fibonacci (N - 2))
   with Subprogram_Variant => (Decreases => N);
end Recursive_Subprograms;
