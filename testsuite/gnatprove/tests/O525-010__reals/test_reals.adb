with Reals; use Reals;

procedure Test_Reals (R : Real)
  with SPARK_Mode
is
begin
   pragma Assert (R * R >= Zero);
end Test_Reals;
