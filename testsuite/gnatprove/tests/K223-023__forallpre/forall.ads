package Forall
is
   type A is array (1..10) of Integer;
   function Get_One (X : A) return Integer
      with Pre => (for all I in X'Range => 1/X(I) = 0),
           Post => (Get_One'Result > 1);
end Forall;
