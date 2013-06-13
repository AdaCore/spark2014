with Pkg_A;

procedure Test_03
with Global => (Output => Pkg_A.State)
is
begin
   Pkg_A.Init;
   Pkg_A.Do_Stuff;
end Test_03;
