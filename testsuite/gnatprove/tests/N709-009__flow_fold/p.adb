package body P is
   type T is record
      A, B : Boolean;
   end record;

   X : T := (A => False, B => False);
   Y : Boolean := False;

   procedure Proc (Z : out Boolean)
     with Global  => (Input => X, Proof_In => Y),
          Depends => (Z => X)
   is
   begin
      Z := X'Update (A => Y).B;
      --  Read of Y has no effect
   end;
end;
