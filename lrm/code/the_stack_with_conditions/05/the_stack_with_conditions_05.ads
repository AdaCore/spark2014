-- This is package is essentially demonstrating simple data abstraction but with
-- the addition of preconditions so that the subprograms can be proven to be
-- free of RTE.
-- The own variable has to be typed because FDL does not allow functions
-- with global variables.  An equivalent FDL function is implicitly declared for
-- each Ada function with the global variables converted to parameters.
-- These parameters need to be typed, hence the declaration of a SPARK abstract
-- type.  The FDL version of of the function has to be used in proof contexts.
package the_stack_with_conditions_05
--# own State : Stack;  -- Abstraction of internal state of the package
--# initializes State;  -- We are asserting it will be initialized
is
   --# type Stack is abstract;      -- Notional type of the global own variable

   function Is_Empty return Boolean;
   --# global State; -- Functions declared  in terms of global

   function Is_Full return Boolean;
   --# global State; -- abstract own variable

   function Top return Integer;
   --# global State;                -- Global and formal contracts
   --# pre not Is_Empty (State);    -- We can now refer to the implicitly
                                    -- declared functions

   procedure Push(X: in Integer);
   --# global in out State;
   --# pre not Is_Full (State);

   procedure Pop(X: out Integer);
   --# global in out State;
   --# pre not Is_Empty (State);

   procedure Swap (X: in Integer);
   --# global in out State;
   --# pre not Is_Empty (State);

end the_stack_with_conditions_05;
