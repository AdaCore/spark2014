procedure Imprecise_GG with SPARK_Mode is
   G : Integer;

   procedure Init with Pre => True;
   procedure Read with Pre => True;
   procedure Init_And_Read with Pre => True;
   procedure Foo with Global => (Output => G);

   procedure Init is
   begin
      G := 0;
   end Init;

   procedure Read is
      L : Integer := G;
   begin
      null;
   end Read;

   procedure Init_And_Read is
   begin
      Init;
      Read;
   end Init_And_Read;

   procedure Foo is
   begin
      Init_And_Read;
   end Foo;
begin
   null;
end Imprecise_GG;
