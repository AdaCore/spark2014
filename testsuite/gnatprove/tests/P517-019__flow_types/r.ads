package R is
   X : Integer := 0;
   subtype T1 is Integer with Predicate => T1 > X;
   subtype T2 is T1      with Predicate => True;   -- This expression is fine,
   --  an error on T1 is enough.

   type T3 (D : Integer := X);
   type T3 (D : Integer := X) is null record;
   --  for discriminants of private types we flag the declaration, while
   --  for discriminants of incomplete types we flag the completion
   --  this is slightly inconsistent, but acceptable (especially, if
   --  it makes the implementation code easier or simpler)

   type T4;
   type T4 is new String (1 .. X);
end;
