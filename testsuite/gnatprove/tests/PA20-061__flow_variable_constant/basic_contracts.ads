package Basic_Contracts is

   function Average (Numerator : Natural;
                     Denominator : Positive) return Float
      with Post => (Average'Result >= 0.0);

end Basic_Contracts;
