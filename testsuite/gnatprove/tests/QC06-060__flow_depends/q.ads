package Q is

   type R is record
      C : Integer;
   end record;

   X : Integer := 0;

   procedure Dummy (Y : out R) with Global => (Proof_In => X);

end;
