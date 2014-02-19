package body Foo
is

   type Value_Kind is (None, Bool, Int);

   type Value (Kind : Value_Kind := None) is record
      case Kind is
         when None =>
            null;
         when Bool =>
            Bool_Field : Boolean;
         when Int =>
            Int_Field  : Integer;
      end case;
   end record;

   type Record_A is record
      X : Value (Bool);
      Y : Value (Int);
      Z : Value (None);
   end record;

   type Record_B (Kind : Value_Kind) is record
      F : Value (Kind);
   end record;

   procedure Test_01_Ok (V : in out Record_A)
   is
   begin
      V.X.Bool_Field := V.Y.Int_Field >= 0;
   end Test_01_Ok;

   procedure Test_02_Ok (V : in out Record_B)
   is
   begin
      V.F.Bool_Field := False;
   end Test_02_Ok;

end Foo;
