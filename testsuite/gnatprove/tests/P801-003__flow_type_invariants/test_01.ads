package Test_01 with Elaborate_Body is

   type T is private;

private

   type T is record
      A : Boolean;
      B : Boolean;
   end record
   with Type_Invariant => T.A xor T.B;

end Test_01;
