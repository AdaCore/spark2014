with Test_Pack; use Test_Pack;
with Ada.Unchecked_Conversion;
procedure Wibble
is
  type U32 is mod 2 ** 32;
  function To_Fp is new Ada.Unchecked_Conversion (Source => U32,
                                                  Target => Float);
  X : Pid_Obj := (Desired => To_Fp (2#01111111011111111111111101110110#),
                  Error   => 0.0);
begin
  Pid_Update (X, To_Fp (2#11110111000010011000000000000000#));
end Wibble;
