with Pkg_A;

procedure Test_02
with Global => (Output => Pkg_A.State)   -- OK
is
begin
   Pkg_A.Do_Stuff;  --  error
end Test_02;
