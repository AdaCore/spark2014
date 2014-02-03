package body Foo
is

   procedure Test_01_Ok (A : in String;
                         B : out Natural)
   with Depends => (B => A)
   is
   begin
      B := A'Length;
   end Test_01_Ok;

   procedure Test_02_Ok (A : in String;
                         B : out Natural)
   with Depends => (B => A)
   is
      Tmp : String := A & "foo";

      procedure P (X : out Natural)
      with Global => Tmp,
           Depends => (X => Tmp)
      is
      begin
         X := Tmp'Length;
      end P;

   begin
      P (B);
   end Test_02_Ok;

end Foo;
