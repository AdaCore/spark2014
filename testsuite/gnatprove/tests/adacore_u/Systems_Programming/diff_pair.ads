package Diff_Pair
  with SPARK_Mode
is
   type Pair is record
      U, V : Natural;
   end record
     with Predicate => U /= V;

   X : Pair with Atomic, Async_Readers, Async_Writers;

   function Max return Integer with
     Volatile_Function,
     Post => Max'Result /= 0;

   function Max2 return Integer with
     Volatile_Function,
     Post => Max2'Result /= 0;

end Diff_Pair;
