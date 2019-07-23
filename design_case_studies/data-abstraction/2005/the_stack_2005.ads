-- This package shows a package declaration which has simple own variable
-- (state abstraction) in SPARK 2005.
-- Note that the own variable "State" does not require to be typed as
-- it can only be used in global and optionally derives annotations within the
-- package specification.
-- The initializes annotation asserts that "State" will be given an initial value
-- during package elaboration. The absence of an initializes annotation asserts
-- that the "State" will not be given an initial value.
-- The state of a package may be represented by more than one own variable but
-- all the state of the package must be encompased by the own variables and the
-- constituent state of each own variable must be mutually exclusive.
package The_Stack_2005
--# own State;          -- Abstraction of internal state of the package
--# initializes State;  -- We are asserting it will be initialized
is
   function Is_Empty return Boolean;
   --# global State; -- Functions declared  in terms of global

   function Is_Full return Boolean;
   --# global State; -- abstract own variable

   procedure Push(X: in Integer);
   --# global in out State;         -- Global and formal contracts

   procedure Pop(X: out Integer);
   --# global in out State;

   procedure Swap(X: in Integer);
   --# global in out State;

end The_Stack_2005;
