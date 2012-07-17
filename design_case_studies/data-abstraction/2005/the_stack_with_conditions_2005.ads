-- This is package is essentially demonstrating simple data abstraction but with
-- the addition of preconditions so that the subprograms can be proven to be
-- free of RTE.
-- The own variable has to be typed becaus SPARK 2005 does not allow functions
-- with global variables.  An equivalent function is implicitly declared with
-- the global variables converted to parameters.
-- These parameters need to be typed, hence the declaration of a SPARK abstract
-- type.
package The_Stack_With_Conditions_2005
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
   --# post (Top (State~) = X) -> (State = State~);
   -- We can refer to the the initial and final value of State.

end The_Stack_With_Conditions_2005;
