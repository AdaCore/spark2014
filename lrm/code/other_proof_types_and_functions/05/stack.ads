package Stack
--# own State : Abstract_Stack;
is

   --  Proof functions to indicate whether or not the Stack is empty
   --  and whether or not it is full.
   --# type Abstract_Stack is abstract;
   --# function Is_Empty (Input : Abstract_Stack) return Boolean;
   --# function Is_Full (Input : Abstract_Stack) return Boolean;

   --  Post-condition indicates that the stack will be
   --  non-empty after pushing an item on to it, while the pre-condition
   --  requires it is not full when we push a value onto it.
   procedure Push(X : in Integer);
   --# global in out State;
   --# pre not Is_Full (State);
   --# post not Is_Empty (State);

   --  Other operations not included as not needed for
   --  this example.


private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   type Stack_Type is
      record
         S : Vector;
         Pointer : Pointer_Range;
      end record;
end Stack;
