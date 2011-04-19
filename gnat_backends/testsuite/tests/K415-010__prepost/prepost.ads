package Prepost is

   function Is_Zero (X : Integer) return Boolean
   is (X = 0);

   function F (Z : Integer) return Boolean
      with Pre => (Z /= 1 and then Is_Zero (Z));

end Prepost;
