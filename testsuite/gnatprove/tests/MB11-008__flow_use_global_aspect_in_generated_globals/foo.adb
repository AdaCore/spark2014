package body Foo
is

   A : Integer;
   B : Integer;

   --  generated global should be [a]
   procedure Gen_1
   is
   begin
      A := A + 1;
   end Gen_1;

   --  correct
   procedure Verify_Gen_1_1
   with Global  => (In_Out => A),
        Depends => (A => A)
   is
   begin
      Gen_1;
   end Verify_Gen_1_1;

   --  incorrect
   procedure Verify_Gen_1_2
   with Global => null
   is
   begin
      Gen_1;
   end Verify_Gen_1_2;

   ----------------------------------------------

   --  generated global should be [a]
   procedure Gen_2
   is
   begin
      Gen_1;
   end Gen_2;

   --  correct
   procedure Verify_Gen_2_1
   with Global  => (In_Out => A),
        Depends => (A => A)
   is
   begin
      Gen_2;
   end Verify_Gen_2_1;

   --  incorrect
   procedure Verify_Gen_2_2
   with Global => null
   is
   begin
      Gen_2;
   end Verify_Gen_2_2;

   ----------------------------------------------

   --  error here
   procedure Liar
   with Global => (In_Out => B)
   is
   begin
      Gen_1;
   end Liar;

   --  generated global should be [b]
   procedure Gen_3
   is
   begin
      Liar;
   end Gen_3;

   --  correct
   procedure Verify_Gen_3_1
   with Global  => (In_Out => B),
        Depends => (B => B)
   is
   begin
      Gen_3;
   end Verify_Gen_3_1;

   --  incorrect
   procedure Verify_Gen_3_2
   with Global => null
   is
   begin
      Gen_3;
   end Verify_Gen_3_2;

   ----------------------------------------------

   --  generated global should be [b]
   procedure Gen_4
   is
   begin
      Gen_3;
   end Gen_4;

   --  correct
   procedure Verify_Gen_4_1
   with Global  => (In_Out => B),
        Depends => (B => B)
   is
   begin
      Gen_4;
   end Verify_Gen_4_1;

   --  incorrect
   procedure Verify_Gen_4_2
   with Global => null
   is
   begin
      Gen_4;
   end Verify_Gen_4_2;

end Foo;
