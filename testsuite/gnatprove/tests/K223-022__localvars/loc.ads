package Loc is
   function Local (Z : Integer) return Integer
      with Pre => (Z = 1),
           Post => (Local'Result = 1);

end Loc;
