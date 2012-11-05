-- This package demonstrates that postconditions as well as preconditions
-- may be applied to a state abstraction. The state abstraction "State"
-- does not need to be typed as State is never mentioned in the proof
-- contracts.
-- The package also shows how the enhanced conditional global contract may be
-- used to show that the value of stack is unchanged in a call to Swap
-- if X = Top.
-- The contracts are execuatble.
package the_stack_with_more_conditions_14
   with Abstract_State    => State,
        Initializes       => State,
        Initial_Condition => Is_Empty
is
   function Is_Empty return Boolean
      with Global => State;

   function Is_Full return Boolean
      with Global => State;

   function Top return Integer
      with Global => State,
           Pre    => not Is_Empty;

   procedure Push (X: in Integer)
      with Global => (In_Out => State),
           Pre    => not Is_Full,
           Post   => Top = X;                     -- A simple post condition


   procedure Pop (X: out Integer)
       with Global => (In_Out => State),
            Pre    => not Is_Empty;

   procedure Swap (X : in Integer)
      with Global => (Input  => State,
                      Output => (if Top /= X then State)), 
                             -- conditional global contract
                             -- indicating that Stack is only
                             -- an output if X /= Top.
           Pre    => not Is_Empty,
           Post   => Top = X;
end the_stack_with_more_conditions_14;
