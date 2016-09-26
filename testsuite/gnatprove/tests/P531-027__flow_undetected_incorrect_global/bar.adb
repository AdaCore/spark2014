package body Bar with SPARK_Mode
is

   --  Should raise error (contract says we inly read Foo.State)
   procedure Get_Data (X : out Integer)
   is
   begin
      Foo.Update;
      X := foo.read;
   end Get_Data;

   G : Integer;

   --  All is OK
   procedure Set_G
   with Global => (Output => G)
   is
   begin
      G := 0;
   end Set_G;

   --  Error: Must not write to G
   procedure Test_01 (X : out Integer)
   with Global => G
   is
   begin
      G := 0;
      X := G;
   end Test_01;

   --  Error: Must not write to G
   procedure Test_02 (X : out Integer)
   with Global => G
   is
   begin
      Set_G;
   end Test_02;

end Bar;
