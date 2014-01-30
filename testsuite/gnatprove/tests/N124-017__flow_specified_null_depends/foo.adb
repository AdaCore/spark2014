package body Foo
is

   type R is record
      X : Integer;
   end record;

   G : R;

   procedure Test_01_Ok (X : in out Integer)
   with Global => null,
        Depends => (X => null,
                    null => X)
   is
   begin
      X := 0;
   end Test_01_Ok;

   procedure Test_02_Ok (X : in Integer)
   with Global => (In_Out => G),
        Depends => (G => X,
                    null => G)
   is
   begin
      G.X := X;
   end Test_02_Ok;

   --  X is actually unused here
   procedure Test_03_E (X : in Integer)
   with Global => (In_Out => G),
        Depends => (G => G,
                    null => X)
   is
   begin
      G.X := G.X + 1;
   end Test_03_E;

   procedure Test_04_Ok (X : in Integer)
   with Global => (In_Out => G),
        Depends => (G => G,
                    null => X)
   is
      Tmp : Integer;
   begin
      --  Wait a while
      for I in Integer range 1 .. X loop
         Tmp := I;  -- still ineffective
      end loop;

      --  Then do something
      G.X := G.X + 1;
   end Test_04_Ok;

   procedure Test_05_E (X, Y : in Integer) -- and Y is actually unused
   with Global => (In_Out => G),
        Depends => (G => G,
                    null => (X, Y))  -- wrong
   is
   begin
      G.X := G.X + X;
   end Test_05_E;

end Foo;
