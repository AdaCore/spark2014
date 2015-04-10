-- This package shows the traditional way of modelling relationships and
-- functional properties of an abstract own variable in SPARK 2005.
-- It combines (muddles?) the ideas of state abstraction and abstract modelling.
package The_Stack_Model
--# own State : Stack;  -- Abstraction of internal state of the package
--# initializes State;  -- We are asserting it will be initialized
is
   --# type Stack is abstract;

   --# function Head (S : Stack) return Integer;
   --# function Tail (S : Stack) return Stack;

   function Is_Empty return Boolean;
   --# global State; -- Functions declared  in terms of global

   function Is_Full return Boolean;
   --# global State; -- abstract own variable

   function Top return Integer;
   --# global State;
   --# pre not Is_Empty (State);
   --# return Head (State);

   procedure Push(X: in Integer);
   --# global in out State;         -- Global and formal contracts
   --# pre not Is_Full (State);
   --# post Head (State) = X and Tail (State) = State~;

   procedure Pop(X: out Integer);
   --# global in out State;
   --# pre not Is_Empty (State);
   --# post State = Tail (State~);

   procedure Swap (X: in Integer);
   --# global in out State;
   --# pre not Is_Empty (State);
   --# post Head (State) = X and Tail (State) = Tail (State~);

end The_Stack_Model;
