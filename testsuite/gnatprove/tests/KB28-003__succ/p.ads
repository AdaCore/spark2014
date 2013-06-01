package P is
   type T is (A, B, C, D);

   function Id_Not_A (X : T) return T
      with Pre  => (X /= A),
           Post => (Id_Not_A'Result = X);

   function Id_Not_D (X : T) return T
      with Pre  => (X /= D),
           Post => (Id_Not_D'Result = X);

   function Id_Gen (X : T) return T
      with Post => (Id_Gen'Result = X);
end P;
