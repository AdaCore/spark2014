package P with SPARK_Mode is

   type E is (A,B,C);
   subtype E1 is E with Static_Predicate => E1 in A | B;
   subtype E2 is E with Static_Predicate => E2 in A;
   subtype E3 is E2 with Static_Predicate => E3 in E1;

end P;
