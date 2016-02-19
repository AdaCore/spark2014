package P2 is

   function Not_In_SPARK return Boolean with SPARK_Mode => Off;

   type T is new Integer with Predicate => Fun and then Not_In_SPARK;

   type T2 is record
      C : T;
   end record;

   G : T2;

   function Fun return Boolean with Global => G;

end;
