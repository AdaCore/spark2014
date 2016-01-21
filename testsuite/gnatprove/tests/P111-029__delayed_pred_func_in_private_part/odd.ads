package Odd
  with SPARK_Mode => On
is
   --function Not_In_SPARK (X : access Integer := null) return Boolean;
   function Not_In_SPARK return Boolean with SPARK_Mode => Off;

   type T is null record with Predicate => Not_In_SPARK;
private
   pragma SPARK_Mode (On);

   --  ??? tPredicate body is inserted here!
end;
