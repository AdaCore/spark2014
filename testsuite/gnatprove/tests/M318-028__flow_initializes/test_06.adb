with Pkg_B;

procedure Test_06
with Global => (In_Out => Pkg_B.State)
is
begin
   Pkg_B.Do_Stuff;
end Test_06;
