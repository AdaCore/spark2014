package Base is
   function Double (x : Integer) return Integer
      with Pre => (X = 3);
end Base;
