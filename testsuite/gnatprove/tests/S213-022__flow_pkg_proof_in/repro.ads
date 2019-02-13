package Repro
with
  Abstract_State => State,
  Initializes    => State
is

private

   type Byte is new Integer;

   function Get_Foo return Byte
   with Global => (Input => State);

end Repro;
