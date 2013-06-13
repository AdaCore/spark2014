with Pkg_B;

procedure Test_05
with Global => (In_Out => Pkg_B.State)
is
begin
   Pkg_B.Init; -- Ineffective import of Pkg_B.State
   Pkg_B.Do_Stuff;
end Test_05;
