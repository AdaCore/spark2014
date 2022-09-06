procedure Main is

  type A is array (0 .. 1) of Integer;
  subtype B is A with Predicate => B(0) > 0 and then B(1) = 42;

  procedure Array_Predicate (X : A)
    with Unreferenced
  is
  begin
    pragma Assert (X in B);  --  @ASSERT:FAIL @COUNTEREXAMPLE
  end Array_Predicate;

  subtype Int is Integer with Predicate => Int in 5 | 8 .. 10 | 40 + 2;

   type R is record
      A : Integer;
      B : Integer;
   end record;

   subtype S is R with Predicate => S.A /= 0 and then S.B in Int;

   procedure Record_Predicate (X : R)
     with Unreferenced
   is
   begin
      pragma Assert (X in S);  --  @ASSERT:FAIL @COUNTEREXAMPLE
   end Record_Predicate;

   procedure Int_Predicate (X : Integer)
     with Unreferenced
   is
   begin
     pragma Assert (X in Int);  --  @ASSERT:FAIL @COUNTEREXAMPLE
   end Int_Predicate;

begin
  null;
end Main;
