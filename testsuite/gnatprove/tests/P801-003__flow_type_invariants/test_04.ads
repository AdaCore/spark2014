package Test_04 with Elaborate_Body is

   type T is private;

private

   C : Boolean := True;

   type T is record
      A : Boolean := True;
      B : Boolean := True;
   end record
   with Type_Invariant => T.A xor T.B xor C;  --  Not OK

end Test_04;
