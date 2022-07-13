package Types_And_Subtypes_Illegal
  with SPARK_Mode
is
   type T0 is private;

   type T1 is tagged private;

   type T2 is tagged record
      F1 : Integer;
   end record;

   procedure Op (X : in T1'Class);

   function Foo return Integer
     with Global   => null,
          Annotate => (GNATprove, Always_Return);

   subtype One_To_Ten is Integer range 1 .. 10
     with Dynamic_Predicate => Foo < 100;
private
   type T0 is new Integer;

   type T1 is tagged null record;
end Types_And_Subtypes_Illegal;
