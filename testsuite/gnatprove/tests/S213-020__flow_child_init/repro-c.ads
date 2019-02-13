package Repro.C
with
  Abstract_State => CState,
  Initializes    => (CState => Repro.State)
is

   procedure Baz
   with
     Global => (In_Out => (CState, Repro.State));

end Repro.C;
