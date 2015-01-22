package body Foo
is
   pragma Warnings (Off, "analyzing unreferenced procedure *");

   function Foo (X : Natural) return Natural
   is
      Tmp_A : Natural := X;
   begin
      Tmp_A := Tmp_A / 2;
      return Tmp_A;
   end Foo;

   function Bar (X : Natural) return Natural
   with Global => null
   is
      Tmp_A : Natural := X;
   begin
      Tmp_A := Tmp_A / 2;
      return Tmp_A;
   end Bar;

   procedure Test_01 (A : Natural;
                      B : out Natural)
   with Depends => (B => A)
   is
      Tmp_B : constant Natural := Foo (A);
      subtype U is Natural range 0 .. Tmp_B;
   begin
      B := U'Last;
   end Test_01;

   procedure Test_02 (A : Natural;
                      B : out Natural)
   with Depends => (B => A)
   is
      Tmp_B : constant Natural := Bar (A);
      subtype U is Natural range 0 .. Tmp_B;
   begin
      B := U'Last;
   end Test_02;

   procedure Test_03 (A : out Natural)
   is
      Tmp_B : constant Natural := Foo (12);
   begin
      A := Tmp_B;
   end Test_03;

end Foo;
