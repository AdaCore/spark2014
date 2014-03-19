procedure Foo (A, B : Integer;
               C    : out Integer)
with
   Global  => null,
   Depends => (C    => A,
               null => B)
is
   function F return Integer is (A) with
      Global => (Input    => A,
                 Proof_In => B),
      Pre => B > 0;
begin
   C := F;
end Foo;
