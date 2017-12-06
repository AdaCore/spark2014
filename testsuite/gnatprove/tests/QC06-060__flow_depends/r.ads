package R is

   type R is record
      C : Integer;
   end record;

   X : R := (C => 0);

   procedure Dummy (Y : out R) with Global => (Proof_In => X);

end;
