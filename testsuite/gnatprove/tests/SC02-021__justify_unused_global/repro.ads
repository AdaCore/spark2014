package Repro
with
   Abstract_State => State,
   Initializes    => State
is
   procedure Foo (Value : out Natural)
   with
      Global  => (Input => State),
      Depends => (Value => State);
end Repro;
