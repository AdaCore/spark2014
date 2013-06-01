package Forall
is
   type A is array (1..10) of Integer;
   function Get_Zero (X : A) return Integer
      with Pre => (for all I in X'Range => X(I) = 0),
           Post => (Get_Zero'Result = 0);

   function Has_Zero (X : A) return Integer
      with Pre => (for some I in X'Range => X(I) = 0),
           Post => (Has_Zero'Result = 0);
end Forall;
