--  This package demonstrates simple data abstraction with the
--  addition of preconditions so that the subprograms can be proven to
--  be free of RTE. Note that the state abstraction "State" does not
--  need to be typed as it is only referenced in the global and
--  optionally derives contracts of the package specification. Indeed
--  a state abstraction never needs typing for this reason. As
--  functions with global variables can be called within contracts the
--  State abstraction "State" does not need to be explicitly mentioned
--  in proof contracts. In the initializes contract we have asserted
--  that the initialized "State" will satisfy the predicate
--  "Is_Empty". This feature is sadly lacking from SPARK 2005 and is
--  required for proof. It is not possible to talk about State'Old,
--  for instance State = State'Old as State is purely an abstraction
--  and is not a variable or function and so we cannot describe that
--  the stack is unchanged in Swap if X = Top in the postcondition
--  (but see next example). The proof contracts within this package
--  are executable.

package the_stack_with_conditions_14
  with SPARK_Mode,
       Abstract_State => State,
       Initializes => State,
       Initial_Condition => Is_Empty
is
   function Is_Empty return Boolean
     with Global => State;

   function Is_Full return Boolean
     with Global => State;

   function Top return Integer
     with Global => State,
          Pre    => not Is_Empty;
   --  Functions with global variables may be called directly within
   --  proof contracts

   procedure Push(X: in Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Full;

   procedure Pop(X: out Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Empty;

   procedure Swap (X : in Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Empty;
end the_stack_with_conditions_14;
