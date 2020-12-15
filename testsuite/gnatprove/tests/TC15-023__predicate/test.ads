package Test with
  SPARK_Mode
is
   type Foo (X : Positive := Positive'First) is private;

   procedure Initialize (Context : out Foo; X : Positive)
   with Pre => not Context'Constrained;

private

   type Foo (X : Positive := Positive'First) is
      record
         Y : Positive := 2;
   end record with
     Dynamic_Predicate => (X < Y);

end Test;
