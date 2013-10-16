with Pkg_B;

procedure Test_04
with Global => (Output => Pkg_B.State)
is
begin
   Pkg_B.Init;
   Pkg_B.Do_Stuff;
end Test_04;
