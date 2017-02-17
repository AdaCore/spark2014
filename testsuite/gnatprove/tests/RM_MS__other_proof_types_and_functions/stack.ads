package Stack
  with SPARK_Mode,
       Abstract_State    => State,
       Initializes       => State,
       Initial_Condition => Is_Empty
is
   --  In SPARK 2014 we can specify an initial condition for the
   --  elaboration of a package and so initialization may be done
   --  during the elaboration of the package Stack, rendering the need
   --  for an initialization procedure unnecessary.

   --  Abstract states do not have types in SPARK 2014 they can only
   --  be directly referenced in Global and Depends aspects.

   --  Proof functions are actual functions but they may have the
   --  convention Ghost meaning that they can only be called from
   --  assertion expressions, e.g., pre and postconditions
   function Max_Stack_Size return Natural
     with Ghost;

   -- Returns the number of elements on the stack
   function Count return Natural
     with Global     => (Input => State),
          Ghost;

   --  Returns the Nth entry on the stack. Stack_Entry (Count) is the
   --  top of stack
   function Stack_Entry (N : Natural) return Integer
     with Global     => (Input => State),
          Pre        => N in 1 .. Count,
          Ghost;
   --  A body (refined) version of this function can (must) be
   --  provided in the body of the package.

   function Is_Empty return Boolean is (Count = 0)
     with Global     => State,
          Ghost;

   function Is_Full return Boolean is (Count = Max_Stack_Size)
     with Global     => State,
          Ghost;

   --  The precondition requires the stack is not full when a value,
   --  X, is pushed onto it. Functions with global items (Is_Full
   --  with global State in this case) can be called in an assertion
   --  expression such as the precondition here.  The postcondition
   --  indicates that the count of the stack will be incremented after
   --  a push and therefore the stack will be non-empty.  The item X
   --  is now the top of the stack.
   procedure Push (X : in Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Full,
          Post   => Count = Count'Old + 1 and
                    Count <= Max_Stack_Size and
                    Stack_Entry (Count) = X;

   --  The precondition requires the stack is not empty when we pull a
   --  value from it. The postcondition indicates the stack count is
   --  decremented.
   procedure Pop (X : out Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Empty,
          Post   => Count = Count'Old - 1;

   --  Procedure that swaps the top two elements in a stack.
   procedure Swap2
     with Global => (In_Out => State),
          Pre    => Count >= 2,
          Post   => Count = Count'Old and
                    Stack_Entry (Count) = Stack_Entry (Count - 1)'Old and
                    Stack_Entry (Count - 1) = Stack_Entry (Count)'Old;
end Stack;
