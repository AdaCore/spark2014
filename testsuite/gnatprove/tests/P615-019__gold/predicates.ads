package Predicates is

   type Even is new Integer
     with Predicate => Even mod 2 = 0;

   subtype Simple_String is String
     with Predicate => Simple_String'First = 1 and Simple_String'Last in Natural;

   type Sorted is array (1 .. 10) of Integer
     with Predicate => (for all J in 1 .. 9 => Sorted(J) <= Sorted(J+1));

   type Name (Size : Positive) is record
      Data : String(1 .. Size);
      Last : Positive;
   end record
     with Predicate => Last <= Size;

end Predicates;
