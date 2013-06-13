with Pkg_A;

procedure Test_01
with Global => (In_Out => Pkg_A.State)   -- not allowed
is
begin
   Pkg_A.Do_Stuff;
end Test_01;
