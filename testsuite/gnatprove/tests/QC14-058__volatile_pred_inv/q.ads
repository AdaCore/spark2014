package Q is
   type T1 is new Integer with Predicate => True;
   type T2 is new T1 with Volatile;
   type T3 is new T2;
end;
