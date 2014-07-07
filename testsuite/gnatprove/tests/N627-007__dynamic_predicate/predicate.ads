package Predicate with SPARK_Mode is

   type Str is new String
     with Dynamic_Predicate => (for all C of Str => C in 'a' .. 'b');

   procedure Call (Value : Str);

end Predicate;
