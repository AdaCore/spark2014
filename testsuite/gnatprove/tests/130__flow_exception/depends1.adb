procedure Depends1
  with Global => null
is
   procedure Test
     (A, B : Integer;
      X, Y : out Integer)
   with
     Always_Terminates => True,
     Depends => (X => A, Y => B),
     Exceptional_Cases => (Program_Error => True),
     Import;

   X, Y : Integer;

begin
   Test (123, 321, X, Y);
exception
   when Program_Error =>
      null;
end;
