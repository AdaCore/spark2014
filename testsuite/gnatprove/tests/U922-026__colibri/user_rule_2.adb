procedure User_Rule_2 (X, Y, Z : Float;
                       Res     : out Boolean)
is
begin
   pragma Assume (X >= 0.0);
   pragma Assume (Y >= 0.0);
   pragma Assume (Z >= 0.0);
   pragma Assume (X <= 16777216.0);
   pragma Assume (Y <= 16777216.0);
   Res := - (X * Y) < Z;
   pragma Assert (Res); --@ASSERT:FAIL
end User_Rule_2;
