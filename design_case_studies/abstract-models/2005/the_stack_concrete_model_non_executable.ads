-- In this package the ideas of data abstraction and abstract modelling have
-- been separated in a similar way as proposed for SPARK 2014 using a concrete
-- Ada type for the model.  This version uses the more natural model for
-- SPARK 2005 in that the functions To_Model, Head and Tail are non-executable
-- proof functions
package The_Stack_Concrete_Model_Non_Executable
--# own State : Stack;  -- Abstraction of internal state of the package
--# initializes State;  -- We are asserting it will be initialized
is
   --# type Stack is abstract;

   type Stack_Model is private;

   --# function To_Model (The_Stack : Stack) return Stack_Model;
   --# function Head (The_Stack : Stack) return Integer;
   --# function Tail (The_Stack : Stack) return Stack_Model;


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
   --# post Head (State) = X and
   --#      Tail (State) = To_Model (State~);

   procedure Pop(X: out Integer);
   --# global in out State;
   --# pre not Is_Empty (State);
   --# post X               = Head (State~) and
   --#     To_Model (State) = Tail (State~);

   procedure Swap (X: in Integer);
   --# global in out State;
   --# pre not Is_Empty (State);
   --# post Head (State) = X and
   --#      Tail (State) = Tail (State~);

private
   type Stack_Model is record
      Value : Natural;
   end record;

end  The_Stack_Concrete_Model_Non_Executable;
