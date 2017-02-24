package Assume_Call is

   function f1 (X : Integer) return Integer
     with Post => f1'Result = X + 1;

end Assume_Call;
