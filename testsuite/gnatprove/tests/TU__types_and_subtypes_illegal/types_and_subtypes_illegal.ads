package Types_And_Subtypes_Illegal
  with SPARK_Mode
is
   -- TU: 1. A Dynamic_Predicate aspect shall not occur in an aspect specification.
   subtype S1 is Integer
     with Dynamic_Predicate => S1 mod 2 = 0;


   type T0 is private;

   -- TU: 1. A record or private type declaration shall not contain the reserved
   --     word **tagged**.
   type T1 is tagged private;

   type T2 is tagged record
      F1 : Integer;
   end record;

   -- TU: 2. The attribute 'Class shall not be denoted.
   procedure Op (X : in T1'Class);


   function Foo return Integer;

   --  TU: 2. For a type or subtype to be in |SPARK|, all predicate
   --  specifications that apply to the (sub)type must be in |SPARK|.
   --  Notwithstanding any rule to the contrary, a (sub)type is never in
   --  |SPARK| if its applicable predicate is not in |SPARK|.
   subtype One_To_Ten is Integer range 1 .. 10
     with Dynamic_Predicate => Foo < 100;
private
   type T0 is new Integer;

   type T1 is tagged null record;

end Types_And_Subtypes_Illegal;
