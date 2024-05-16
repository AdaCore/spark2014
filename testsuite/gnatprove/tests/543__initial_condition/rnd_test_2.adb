with Ada.Text_IO;
with Random; use Random;

--  The initial condition of withed units should not be known to prove main
--  subprograms themselves.

procedure Rnd_Test_2 with
  Pre => True
is
   X, Y : Random.Random_Bits;
begin
   Random.Initialise; -- @PRECONDITION:FAIL
   Random.Get (X);
   Random.Get (Y);

   Ada.Text_IO.Put_Line("X:" & Random.Random_Bits'Image (X));
   Ada.Text_IO.Put_Line("Y:" & Random.Random_Bits'Image (Y));
end Rnd_Test_2;
