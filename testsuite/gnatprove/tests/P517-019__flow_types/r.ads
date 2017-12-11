package R is
   X : Integer := 0;
   subtype T1 is Integer with Predicate => T1 > X;
   subtype T2 is T1      with Predicate => True;   -- This expression is fine,
   --  an error on T1 would be enough; I wouldn't even bother about this except
   --  that by subtyping and/or type derivation from a private type whose full
   --  view is not is SPARK and has a predicate expression with a SPARK
   --  violation. Then we might accidentally flow-analyse that expression and
   --  crash on a non-supported construct (e.g. pointer equality). However, I
   --  am not sure if such a scenarion is allowed, as currently marking crashes
   --  on that; to be investigated on QC10-002.

   type T3 (D : Integer := X);
   type T3 (D : Integer := X) is null record;
   --  for discriminants of private types we flag the declaration, while
   --  for discriminants of incomplete types we flag the completion
   --  this is slightly inconsistent, but acceptable (especially, if
   --  it makes the implementation code easier or simpler)

   type T4;
   type T4 is new String (1 .. X);
end;
