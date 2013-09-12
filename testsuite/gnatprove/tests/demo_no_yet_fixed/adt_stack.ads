-- This specification is a implementation of a Stack ADT (Abstract Data Type)
-- An ADT defines a set of objects, with a set of operations that characterize
-- the behaviour of those object. Khown well on the name OOP.


package ADT_Stack is pragma SPARK_Mode (On);  

   type Stack is tagged private; -- tagged for extension in child package

   function Is_Empty(S : Stack) return Boolean;
   function Is_Full(S : Stack) return Boolean;

   procedure Clear(S : out Stack);

   procedure Push(S : in out Stack; X : in Integer);
   -- assert,precondition and postcondition are translated in SPARK syntax
   -- pragma Precondition (S.Stack_Top < Stack_Size);
   -- pragma Postcondition (S.Stack_Vector(S.Stack_Top) = X);

   procedure Pop(S : in out Stack; X : out Integer); -- not a function as in ASM_Stack

   Overflow, Underflow : exception; --  Not yet translated

   --  overloading operators = to compare two stack
   function "=" (S, T : Stack) return Boolean; -- Not yet transladed

--  full details of the type Stack
private
   Stack_Size : constant := 100;
   type Stack_Range is new Integer range 0 .. Stack_Size; -- derived type
   type Vector is array(1 .. Stack_Range'Last) of Integer; --  anonymous type
   type Stack is tagged
      record
         STack_Vector  : Vector;
         STack_Top : Stack_Range;
      end record;

end; -- Not necessary to repeat the name of package,it can be generated
