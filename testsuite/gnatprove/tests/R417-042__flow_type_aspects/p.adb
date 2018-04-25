procedure Wrapper (X, Low, High : Integer)
  with Global => null
is
   procedure Test1
     with Global => (Input    => X,
                     Proof_In => (Low, High))
   is
      subtype T is Integer with Predicate => T in Low .. High;

      Y : T;
   begin
      Y := X;
   end Test1;

   procedure Test2
     with Global => (Input    => X,
                     Proof_In => (Low, High))
   is
      subtype T is Integer with Predicate => T in Low .. High;

      Y : T := X;
   begin
      null;
   end Test2;
begin
   null;
end Wrapper;
