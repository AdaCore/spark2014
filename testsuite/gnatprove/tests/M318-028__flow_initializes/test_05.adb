with Pkg_B;

procedure Test_05
with Global => (In_Out => Pkg_B.State) -- Ineffective import of Pkg_B.State
is                                     -- since we initialize it later (i.e.
begin                                  -- this should be an out)
   Pkg_B.Init;
   Pkg_B.Do_Stuff;
end Test_05;
