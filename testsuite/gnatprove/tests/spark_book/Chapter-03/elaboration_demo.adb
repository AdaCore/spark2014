with Ada.Numerics.Elementary_Functions;
procedure Elaboration_Demo (Size  : in Positive;
                            Count : out Natural) is
   Line  : String (1 .. Size) := (others => ' ');
   Guess : Float := (1.0 + Ada.Numerics.Elementary_Functions.Sqrt (5.0)) / 2.0;
begin
   null;
end Elaboration_Demo;
