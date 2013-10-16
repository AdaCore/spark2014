with Pkg_E;

procedure Test_09
with Global => (In_Out => Pkg_E.State)
is
begin
   Pkg_E.Do_Stuff;
end Test_09;
