private package Repro.B
with
  Abstract_State => (BState with Part_Of => Repro.State),
  Initializes    => BState
is

   function Get return Byte
   with Global => (Input => BState);

   procedure Bar
   with Global => (In_Out => BState);

end Repro.B;
