package Subty is

   type My_Enum is (A , B , C , D , E);

   subtype Vowels is My_Enum
   with Static_Predicate => Vowels in A | E;

   subtype Positive_But_Not_Ten is Positive
   with Static_Predicate => Positive_But_Not_Ten /= 10;

   subtype Positive_With_Hole is Positive
   with Static_Predicate => Positive_With_Hole < 10 or Positive_With_Hole > 20;

   subtype Positive_Not_One is Positive
   with Static_Predicate => Positive_Not_One > 1;
end Subty;
