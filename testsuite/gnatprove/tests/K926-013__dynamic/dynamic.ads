package Dynamic is

   type T is array(Integer range <>) of Boolean;

   function P (X : Positive) return Integer
      with Pre =>  (X <= 10),
           Post => (X + 2 <= P'Result and then P'Result <= 10);

end Dynamic;
