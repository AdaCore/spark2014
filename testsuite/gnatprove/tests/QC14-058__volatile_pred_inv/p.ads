package P is

   type T1 is private;

   type T2 is new Integer with
     Volatile,
     Predicate => True;

private

   type T1 is new Integer with
     Volatile,
     Invariant => True;

end P;
