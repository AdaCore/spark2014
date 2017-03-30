
--  This package implements a stack.

with Types; use Types;

package Stack
with SPARK_Mode => On
is

   Overflow  : exception;
   --  Raised if operation Push below is called when the stack is full.

   Underflow : exception;
   --  Raised if operations Pop/Top below are called when the stack is empty.

   function Size return Integer;

   procedure Push (V : Value)
     with Pre => not Full,
     Post => Size = Size'Old + 1;
   --  Pushes value onto the stack.
   --  If the stack is full Stack.Overflow is raised.

   procedure Pop (V : out Value)
     with Pre => not Empty,
     Post => Size = Size'Old - 1;
   --  Pops a value off the stack and returns it. If the pop fails
   --  because the stack is empty Stack.Underflow is raised.

   function Empty return Boolean;
   --  Returns True if the Stack is empty.

   function Full return Boolean;

   procedure Clear;
   --  Empties the stack.

   function Top return Value
   with Pre => not Empty;
   --  Returns the value on top of the stack. If the stack is empty
   --  the exception Stack.Underflow is raised.

   procedure View;
   --  Prints the contents of the Stack on the screen.
   --  Values are printed in the order in which they occur in the Stack.

private


   ----------------
   -- Local Data --
   ----------------

   Max_Size : constant := 200;
   --  The stack size.

   Last : Natural range 0 .. 200 := 0;
   --  Indicates the top of the stack. When 0 the stack is empty.

   function Full return Boolean is (Last >= Max_Size);

   function Empty return Boolean is (Last < 1);

   function Size return Integer is (Last);

end Stack;
