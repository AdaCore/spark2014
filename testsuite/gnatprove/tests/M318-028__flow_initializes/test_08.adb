with Pkg_D;

procedure Test_08
with Global => (In_Out => Pkg_D.State)   -- not allowed
is
begin
   Pkg_D.Do_Stuff;
end Test_08;
