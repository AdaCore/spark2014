package Assert_Loop_05
is
   subtype Index is Integer range 1 .. 10;
   type A_Type is Array (Index) of Integer;

   function Value_present (A: A_Type; X : Integer) return Boolean;
   --# return for some M in Index => (A (M) = X);
end Assert_Loop_05;
