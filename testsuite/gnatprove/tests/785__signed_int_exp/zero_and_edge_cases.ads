package Zero_And_Edge_Cases
  with SPARK_Mode
is

   --  Boundary values for the base and the exponent, including the
   --  RM-mandated convention that X ** 0 = 1 for all X (0 ** 0 included).

   function Any_Power_Zero_Is_One (X : Integer) return Boolean
   with Post => Any_Power_Zero_Is_One'Result;

   function Zero_To_Positive_Power_Is_Zero (N : Positive) return Boolean
   with Pre => N <= 20, Post => Zero_To_Positive_Power_Is_Zero'Result;

   function One_To_Any_Power_Is_One (N : Natural) return Boolean
   with Pre => N <= 20, Post => One_To_Any_Power_Is_One'Result;

   --  Classic alternation lemma: needs induction on N.
   function Minus_One_Alternates (N : Natural) return Boolean
   with Pre => N <= 20, Post => Minus_One_Alternates'Result;

end Zero_And_Edge_Cases;
