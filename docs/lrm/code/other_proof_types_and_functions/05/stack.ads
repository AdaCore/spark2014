package Stack
--# own State : Abstract_Stack;
is
   --  It is not possible to specify that the stack will be
   --  initialized to empty except by having an initialization
   --  subprogram called during program execution (as opposed to
   --  package elaboration).

   --  Proof functions to indicate whether or not the Stack is empty
   --  and whether or not it is full.
   --# type Abstract_Stack is abstract;

   --# function Max_Stack_Size return Natural;

   --  Proof function to give the number of elements on the stack.
   --# function Count(Input : Abstract_Stack) return Natural;

   --  Proof function returns the Nth entry on the stack.
   --  Stack_Entry (Count (State)) is the top of stack
   --# function Stack_Entry (N : Natural; S : Abstract_Stack) return Integer;
   --# pre N in 1 .. Count (S);
   --  A refined version of this function cannot be written because
   --  the abstract view has a formal parameter of type Abstract_Stack
   --  whereas the refined view would not have this parameter but use
   --  a global. A user defined proof rule would be required to define
   --  this function. Alternatively, it could be written as an Ada
   --  function where the the global and formal parameter views would
   --  be available. However, the function would then be callable and
   --  generate implementation code.

   --# function Is_Empty(Input : Abstract_Stack) return Boolean;
   --# return Count (Input) = 0;

   --# function Is_Full(Input : Abstract_Stack) return Boolean;
   --# return Count (Input) = Max_Stack_Size;

   --  The precondition requires the stack is not full when a value, X,
   --  is pushed onto it.
   --  The postcondition indicates that the count of the stack will be
   --  incremented after a push and therefore the stack will be non-empty.
   --  The item X is now the top of the stack.
   procedure Push(X : in Integer);
   --# global in out State;
   --# pre  not Is_Full(State);
   --# post Count (State) = Count (State~) + 1 and
   --#      Count (State) <= Max_Stack_Size and
   --#      Stack_Entry (Count (State), State) = X;

   --  The precondition requires the stack is not empty when we
   --  pull a value from it.
   --  The postcondition indicates the stack count is decremented.
   procedure Pop (X : out Integer);
   --# global in out State;
   --# pre not Is_Empty (State);
   --# post Count (State) = Count (State~) - 1;

   --  Procedure that swaps the first two elements in a stack.
   procedure Swap2;
   --# global in out State;
   --# pre  Count(State) >= 2;
   --# post Count(State) =  Count(State~) and
   --#      Stack_Entry (Count (State), State) =
   --#         Stack_Entry (Count (State) - 1, State~) and
   --#      Stack_Entry (Count (State) - 1, State) =
   --#         Stack_Entry (Count (State), State~);

   --  Initializes the Stack.
   procedure Initialize;
   --# global out State;
   --# post Is_Empty (State);
end Stack;
