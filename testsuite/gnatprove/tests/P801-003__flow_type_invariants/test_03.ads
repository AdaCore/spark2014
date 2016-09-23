package Test_03 with Elaborate_Body is

   type T is private;

   C : Boolean with Constant_After_Elaboration;

private

   type T is record
      A : Boolean := False;
      B : Boolean := False;
   end record
   with Type_Invariant => T.A xor T.B xor C;  --  Not OK, CAE

end Test_03;
