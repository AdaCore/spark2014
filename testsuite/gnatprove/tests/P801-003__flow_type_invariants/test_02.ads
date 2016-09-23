package Test_02 with Elaborate_Body is

   type T is private;

private

   C : constant Boolean := True;

   type T is record
      A : Boolean := True;
      B : Boolean := True;
   end record
   with Type_Invariant => T.A xor T.B xor C;  --  OK, true constant

end Test_02;
