package Pkg
with
   SPARK_Mode     => On,
   Abstract_State => State,
   Initializes    => State
is

   procedure Process
   with
      Global => (In_Out => State),
      Depends => (State =>+ null);

end Pkg;
