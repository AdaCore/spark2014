package Types_And_Subtypes_Illegal
  with SPARK_Mode
is
   function Foo return Integer;

   --  TU: 2. For a type or subtype to be in |SPARK|, all predicate
   --  specifications that apply to the (sub)type must be in |SPARK|.
   --  Notwithstanding any rule to the contrary, a (sub)type is never in
   --  |SPARK| if its applicable predicate is not in |SPARK|.
   subtype One_To_Ten is Integer range 1 .. 10
     with Dynamic_Predicate => Foo < 100;
end Types_And_Subtypes_Illegal;
