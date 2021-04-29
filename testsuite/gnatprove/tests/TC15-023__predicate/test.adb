package body Test with
  SPARK_Mode
is

   procedure Initialize (Context : out Foo; X : Positive)is
   begin
      Context := (X => X, Y => X);  --  @PREDICATE_CHECK:FAIL
   end Initialize;

end Test;
