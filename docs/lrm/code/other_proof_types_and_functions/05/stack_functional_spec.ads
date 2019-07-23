package Stack_Functional_Spec
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
   --# function Stack_Entry (S : Abstract_Stack; N : Natural) return Integer;
   --# pre N in 1 .. Count (S);
   --  A refined version of this function cannot be written because
   --  the abstract view has a formal parameter of type Abstract_Stack
   --  whereas the refined view would not have this parameter but use
   --  a global. A user defined proof rule would be required to
   --  define this function. Alternatively, it could be written as an
   --  Ada function where the the global and formal parameter views
   --  would be available. However, the function would then be
   --  callable and generate implementation code.

   --# function Is_Empty(Input : Abstract_Stack) return Boolean;
   --# return Count (Input) = 0;

   --# function Is_Full(Input : Abstract_Stack) return Boolean;
   --# return Count (Input) = Max_Stack_Size;

   --  The precondition requires the stack is not full when a value, X,
   --  is pushed onto it.
   --  Functions with global items (Is_Full with global State in this case)
   --  can be called in an assertion expression such as the precondition here.
   --  The postcondition indicates that the count of the stack will be
   --  incremented after a push and therefore the stack will be non-empty.
   --  The item X is now the top of the stack and the contents of the rest of
   --  the stack are unchanged.
   procedure Push(X : in Integer);
   --# global in out State;
   --# pre  not Is_Full(State);
   --# post Count (State) = Count (State~) + 1 and
   --#      Count (State) <= Max_Stack_Size and
   --#      Stack_Entry (State, Count (State)) = X and
   --#      (for all I in Natural range 1 .. Count (State~) =>
   --#          (Stack_Entry (State, I) = Stack_Entry (State~, I)));

   --  The precondition requires the stack is not empty when we
   --  pull a value from it.
   --  The postcondition indicates that the X = the old top of stack,
   --  the stack count is decremented, and the contents of the stack excluding
   --  the old top of stack are unchanged.
   procedure Pop (X : out Integer);
   --# global in out State;
   --# pre not Is_Empty (State);
   --# post Count (State) = Count (State~) - 1 and
   --#      X = Stack_Entry (State~, Count (State~)) and
   --#      (for all I in Natural range 1 .. Count (State) =>
   --#          (Stack_Entry (State, I) = Stack_Entry (State~, I)));

   --  The precondition requires that the stack has at least 2 entries
   --  (Count >= 2).
   --  The postcondition states that the top two elements of the stack are
   --  transposed but the remainder of the stack is unchanged.
   procedure Swap2;
   --# global in out State;
   --# pre  Count(State) >= 2;
   --# post Count(State) =  Count(State~) and
   --#      Stack_Entry (State, Count (State)) =
   --#         Stack_Entry (State~, Count (State) - 1) and
   --#      Stack_Entry (State, Count (State) - 1) =
   --#         Stack_Entry (State~, Count (State)) and
   --#      (for all I in Natural range 1 .. Count (State) =>
   --#          (Stack_Entry (State, I) = Stack_Entry (State~, I)));

   --  Initializes the Stack.
   procedure Initialize;
   --# global out State;
   --# post Is_Empty (State);
end Stack_Functional_Spec;
