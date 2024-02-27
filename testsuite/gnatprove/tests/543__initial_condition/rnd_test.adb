with Ada.Text_IO;
with Random; use Random;

--  The initial condition of withed units should be known to prove the
--  precondition of main subprograms.

procedure Rnd_Test
with Pre => not Random.Is_Initialised -- @PRECONDITION_MAIN:PASS
is
   X, Y : Random.Random_Bits;
begin
   Random.Initialise;
   Random.Get (X);
   Random.Get (Y);

   Ada.Text_IO.Put_Line("X:" & Random.Random_Bits'Image (X));
   Ada.Text_IO.Put_Line("Y:" & Random.Random_Bits'Image (Y));
end Rnd_Test;
