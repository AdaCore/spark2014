-- To describe relationships between initial and final values of a state
-- abstraction and to specify the properties of a stack functionally a
-- model of a stack has to be introduced.  The model may abstract or concrete
-- and if it is concrete it may be executable.
-- Note that the state abstraction "State" does not need to be typed.
-- In this example a concrete executable model is defined.  This example shows
-- that for efficiency reasons that it is possible to model a stack purely in
-- terms of a natural number representing the stack pointer.
-- For this model to be sound we must guarantee in the
-- implementation of the stack that all operations only add or remove an element
-- on the top of the stack, or read or update the top element of the stack.
-- All other elements of the stack must be unchanged.
-- The other requirement is that we cannot copy stacks which are being modelled
-- this way.  This is enforced because the the package is an ASM.
-- The contracts are executable.
package The_Stack_Executable_Model
with
  Abstract_State => State,
  initializes => State,
  Initial_Condition => Is_Empty
is

   -- Declare the stack model type
   type Stack_Model is private;

   -- A function to convert between the abstract state and the model
   function Model return Stack_Model
   with
     Global => State;

   function Is_Empty return Boolean
   with
     Global => State;

   function Is_Full return Boolean
   with
     Global => State;

   -- Head and Tail are essentially functions defined purely for proof although
   -- they are executable.
   -- Perhaps we should have an aspect which allows the denotation of functions
   -- which are only to be called within contracts?

   -- The Head function requires a precondition as it is
   -- executable and returns a concrete Ada scalar type.
   function Head return Integer
   with
     Global => State,
     pre => not Is_Empty;

   function Tail return Stack_Model
   with
   Global => State;

   -- The postconditions of Top, Push, Pop and Swap are written in terms of
   -- Head, Tail and Model.

   -- We do not show a relationship between the initial and final values of
   -- the abstract state here because Top is a function and with no side-effects
   -- cannot change the abstract state.
   function Top return Integer
   with
     Global => State,
     Pre  => not Is_Empty,
     Post => Top'Result = Head;

   -- Here we have a relationship between the initial and final values of the
   -- abstract state but it is done indirectly through the stack model using the
   -- conversion routine Model, i.e., Tail = Model'Old.
   procedure Push (X: in Integer)
   with
     Global => (In_Out => State),
     Pre  => not Is_Full,
     Post => Head  = X and
             Tail  = Model'Old;

   -- The relationship is reversed here, Model = Tail'Old.
   procedure Pop (X: out Integer)
   with
     Global => (In_Out => State),
     Pre => not Is_Empty,
     Post => X     = Head'Old and
             Model = Tail'Old;

   -- Here the relationship shows that the Tail of the abstract state does not
   -- change.
   procedure Swap (X : in Integer)
   with
     Global => (In_Out  => State),
     Pre  => not Is_Empty,
     Post => Head = X and
             Tail = Tail'Old;
private
   -- The simplified model is simply a Natural to represent the stack pointer
   type Stack_Model is record
      Value : Natural;
   end record;
end The_Stack_Executable_Model;

