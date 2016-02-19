package Q with SPARK_Mode is

   type T is new Integer with Predicate => Foo (T);

   function Foo (X : T) return Boolean is (True);

end;
