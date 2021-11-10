package Pkg with
  Abstract_State => (State_A),
  Initializes    => (State_A, B)
is
   pragma Elaborate_Body (Pkg);
   B : Integer;
end Pkg;
