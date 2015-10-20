with Interfaces; use Interfaces;

procedure U
  with SPARK_Mode
is
   B : constant Unsigned_8 := 10;

   type Tt7 is mod 3;
   C : constant Tt7 := 2;
begin
   pragma Assert ((C or 1) = 0);

   pragma Assert (Shift_Left(B, 256) = 0);
end U;
