--  This package shows a package declaration which has simple state
--  abstraction in SPARK 2014. Note that the state abstraction "State"
--  does not require to be typed as it can only be used in global and
--  optionally derives contracts within the package specification. The
--  initializes contract asserts that "State" will be given an initial
--  value during package elaboration. The absence of an initializes
--  contract asserts that the "State" will not be given an initial
--  value. The state of a package may be represented by more than one
--  abstraction but all the state of the package must be encompased by
--  the abstractions and the constituent state of each abstraction
--  must be mutually exclusive.

package the_stack_14
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   function Is_Empty return Boolean
     with Global => State;

   function Is_Full return Boolean
     with Global => State;

   function Top return Integer
     with Global => State;

   procedure Push(X: in Integer)
     with Global => (In_Out => State);

   procedure Pop(X: out Integer)
     with Global => (In_Out => State);

   procedure Swap (X : in Integer)
     with Global => (In_Out => State);
end the_stack_14;
