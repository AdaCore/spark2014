with Interfaces;

package Repro
with
  Abstract_State => State,
  Initializes    => State
is

private

   type Byte is new Interfaces.Unsigned_8;

   function Get_Foo return Byte
   with Global => (Input => State);

   function Condition return Boolean
   with Global => (Input => State);

end Repro;
