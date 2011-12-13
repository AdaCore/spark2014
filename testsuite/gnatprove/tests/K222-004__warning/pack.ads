package Pack is
   function F return Boolean
     with Post => not F'Result;
   procedure P;
end;
