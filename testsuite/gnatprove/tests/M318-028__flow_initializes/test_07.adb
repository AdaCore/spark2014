with Pkg_C;

procedure Test_07
with Global => (In_Out => Pkg_C.State)   -- not allowed
is
begin
   Pkg_C.Do_Stuff;
end Test_07;
