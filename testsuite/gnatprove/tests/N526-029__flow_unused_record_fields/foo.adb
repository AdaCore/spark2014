package body Foo
is

   type T is record
      X : Integer;
      Y : Integer;
   end record;

   function Wibble (A : Integer) return T
   with Global => null
   is
   begin
      return (A, A);
   end Wibble;

   procedure Test_01_Ok (N : in out Integer)
   with Global => null
   is
      Tmp : T;
   begin
      Tmp := Wibble (N);
      N   := Tmp.X;
   end Test_01_Ok;

end Foo;
