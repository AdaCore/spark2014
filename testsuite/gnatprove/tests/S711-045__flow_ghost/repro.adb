procedure Repro (X : out Boolean) with Ghost
is
   S : String(1.. 5) := (others => '0');
begin
   S := (others => '1');
   X := S(3) = '1';
end Repro;
