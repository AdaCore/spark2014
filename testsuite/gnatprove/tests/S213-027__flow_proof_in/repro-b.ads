private package Repro.B
with
  Abstract_State => (State with Part_Of => Repro.State),
  Initializes    => State
is

   function Get return Byte
   with
     Global => (Input => Repro.State),
     Pre    => Condition;

end Repro.B;
