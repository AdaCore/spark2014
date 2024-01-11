with Ada.Unchecked_Conversion;

procedure Convf is
   type R1 is new Float with Size => 256;
   type R2 is array (1 .. 8) of Integer;

   function UC is new Ada.Unchecked_Conversion (R1, R2);

   V11, V12 : R1;
   V21, V22 : R2;
begin
   V11 := 0.0;
   V12 := 0.0;
   pragma Assert (V11 = V12);
   V21 := UC(V11);
   V22 := UC(V12);
   pragma Assert (V21 = V22);
end;
