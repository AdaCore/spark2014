package Chars is
   function DoIt return Boolean
      with Post => (DoIt'Result);
end Chars;
