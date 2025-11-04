with Ada.Strings.Bounded;

procedure Main
  with SPARK_Mode
is
   package dummy is new Ada.Strings.Bounded.Generic_Bounded_Length (Max => 15);
begin
   null;
end Main;
