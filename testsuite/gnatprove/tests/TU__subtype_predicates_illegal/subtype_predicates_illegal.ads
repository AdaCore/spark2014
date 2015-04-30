package Subtype_Predicates_Illegal
  with SPARK_Mode
is
   subtype Even is Integer
     with Dynamic_Predicate => Even mod 2 = 0;
end Subtype_Predicates_Illegal;
