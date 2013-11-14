package Stack
--# own State : Abstract_Stack;
is
   --  It is not possible to specify that the stack will be initialized 
   --  to empty except by having an initialization subprogram called
   --  during program executiion (as opposed to package elaboration.
   
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
   --  whereas the refined view would not have this parameter but
   --  use a global.  A user defined proof rule would be required to
   --  define this function.
   --  Alternatively it could be written as an Ada function where the
   --  the global and formal parameter views would be available.
   --  However the function would then be callable and generate implementation 
   --  code.

   --# function Is_Empty(Input : Abstract_Stack) return Boolean;
   --# return Count (Input) = 0;
   
   --# function Is_Full(Input : Abstract_Stack) return Boolean;
   --# return Count (Input) = Max_Stack_Size;
   
   --  Post-condition indicates that the stack will be
   --  non-empty after pushing an item on to it, the new item will be
   --  the top of the stack and the previous top of stack is not changed. 
   --  The pre-condition requires it is not full when we push a value onto it.
   procedure Push(X : in Integer);
   --# global in out State;
   --# pre  not Is_Full(State);
   --# post Count (State) = Count (State~) + 1 and 
   --#      Count (State) <= Max_Stack_Size and
   --#      Stack_Entry (Count (State), State) = X and 
   --#      Stack_Entry (Count (State) - 1, State) = 
   --#      Stack_Entry (Count (State~), State~);

   --  Post-condition indicates that the X = the old top of stack, 
   --  while the pre-condition requires the stack is not empty when we 
   --  pull a value from it.
   procedure Pop (X : out Integer);
   --# global in out State;
   --# pre not Is_Empty (State);
   --# post Count (State) = Count (State~) - 1 and
   --#      X = Stack_Entry (Count (State~), State~);
                        
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

   --  Other operations not included as not needed for
   --  this example.

end Stack;
