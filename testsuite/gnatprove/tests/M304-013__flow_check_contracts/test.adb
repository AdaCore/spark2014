package body Test is

   G : Integer;

   procedure Swap_01 (X, Y : in out Integer)
     with Depends => (X => Y,
                      Y => X)
   is
   begin
      X := Y;
      Y := X;
      --  Well, of course this won't work.
   end Swap_01;

   procedure Test_01
     with Global  => (Output => G),
          Depends => (G => null);

   procedure Test_01
   is
   begin
      G := 10;
   end Test_01;

   procedure Test_02 (X : in out Integer)
     with Global  => (Output => G),
          Depends => (G => null,
                      X => X);

   procedure Test_02 (X : in out Integer)
   is
   begin
      X := X + 1;
   end Test_02;

   procedure Test_03 (X : in out Integer)
     with Global  => (Input => G),
          Depends => (X    => X,
                      null => G);

   procedure Test_03 (X : in out Integer)
   is
   begin
      X := X + 1;
   end Test_03;

   procedure Test_04 (X : in out Integer)
     with Depends => (X    => X,
                      null => G);

   procedure Test_04 (X : in out Integer)
   is
   begin
      X := X + 1;
   end Test_04;

end Test;
