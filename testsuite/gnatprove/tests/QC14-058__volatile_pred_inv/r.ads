package R with SPARK_Mode is
   type B is new Integer with Dynamic_Predicate => True;
   type T is new B with Volatile;
end;
