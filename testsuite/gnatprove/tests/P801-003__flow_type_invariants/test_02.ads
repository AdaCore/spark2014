package Test_02 with Elaborate_Body is

   type T is private;

private

   C : constant Boolean := False;

   type T is record
      A : Boolean;
      B : Boolean;
   end record
   with Type_Invariant => T.A xor T.B xor C;  --  OK, true constant

end Test_02;
