with Repro;

procedure Repro_Main
with
  Global => (In_Out => Repro.State),
  Pre    => Repro.Invariant
is
begin
   Repro.Foo;
end Repro_Main;
