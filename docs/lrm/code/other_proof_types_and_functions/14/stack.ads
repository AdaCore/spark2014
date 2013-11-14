pragma SPARK_Mode (On);
package Stack
  with Abstract_State => State,
       Initializes => State,
       Initial_Condition => not Is_Empty
is
   --  In SPARK 2014 we can specify an initial condition for the
   --  elaboration of a package and so initialization may be done during
   --  the elaboration of the package Stack rendering the need for an
   --  initialization procedure unnecessary

   --  Abstract states do not have types in SPARK 2014
   --  Proof functions are actual functions but they may
   --  have the convention Ghost meaning that they can only
   --  be called from assertion expressions, e.g., pre and postconditions
   function Max_Stack_Size return Natural
     with Convention => Ghost;

   -- Returns the number of elements on the stack
   function Count return Natural
     with Global     => (Input => State),
     Convention => Ghost;

   -- Returns the Nth entry on the stack.
   -- Stack_Entry (Count) is the top of stack
   function Stack_Entry (N : Natural) return Integer
     with Global     => (Input => State),
          Pre        => N in 1 .. Count,
          Convention => Ghost;
   --  A body (refined) version of this function can (must) be provided
   --  in the body of the package.

   function Is_Empty return Boolean is (Count = 0)
     with Global     => State,
         Convention => Ghost;

   function Is_Full return Boolean is (Count = Max_Stack_Size)
     with Global     => State,
          Convention => Ghost;

   --  Post-condition indicates that the stack will be
   --  non-empty after pushing an item on to it, the new item will be
   --  the top of the stack and the previous top of stack is not changed.
   --  The pre-condition requires it is not full when we push a value onto it.
   --  Functions with global items (State in this case) can be called
   --  in an assertion expression.
   procedure Push (X : in Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Full,
          Post   => Count = Count'Old + 1 and Count <= Max_Stack_Size and
                    Stack_Entry (Count) = X and
                    Stack_Entry (Count - 1) = Stack_Entry (Count - 1)'Old;

   --  Post-condition indicates that the X = the old top of stack,
   --  while the pre-condition requires the stack is not empty when we
   --  pull a value from it.
   procedure Pop (X : out Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Empty,
          Post   => Count = Count'Old - 1 and
                    X = Stack_Entry (Count'Old);

   --  Procedure that swaps the top two elements in a stack.
   procedure Swap2
     with Global => (In_Out => State),
          Pre    => Count >= 2,
          Post   => Count = Count'Old and
                    Stack_Entry (Count) = Stack_Entry (Count - 1)'Old and
                    Stack_Entry (Count - 1) = Stack_Entry (Count)'Old;

end Stack;
