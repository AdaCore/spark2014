package Subtype_Predicates_Illegal
  with SPARK_Mode
is
   --  TU: 1. A Dynamic_Predicate aspect shall not occur in an aspect
   --  specification.

   subtype Even is Integer
     with Dynamic_Predicate => Even mod 2 = 0;
end Subtype_Predicates_Illegal;
