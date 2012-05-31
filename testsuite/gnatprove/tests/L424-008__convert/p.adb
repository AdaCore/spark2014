procedure P is
   type Arr is array (Integer range <>) of Integer;
   My_S1 : Arr (1 .. 3) := (1, 2, 3);
   My_S2 : Arr (2 .. 4) := My_S1;
begin
   pragma Assert (My_S2 (2) = 1);
   pragma Assert (My_S2 (2) /= 1);
   pragma Assert (My_S2 (2) = 2);
   pragma Assert (My_S2 (2) /= 2);
end P;
