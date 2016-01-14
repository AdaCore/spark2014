package P3 is

   type T is new Integer with Predicate => Fun;

   type T2 is record
      C : T;
   end record;

   function Fun return Boolean with SPARK_Mode => Off;

end;
