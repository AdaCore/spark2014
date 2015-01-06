package Package_1
with SPARK_Mode => On,
     Abstract_State => State,
     Initializes    => State
is

   ----------------------------------------------------------------------------
   --  Invariant
   ----------------------------------------------------------------------------
   function Invariant return Boolean
     with Global => (Input => State);

   ----------------------------------------------------------------------------
   --  Update
   ----------------------------------------------------------------------------
   procedure Update
     with Global => (In_Out => State),
          Pre    => (Invariant),
          Post   => (Invariant);

end Package_1;
