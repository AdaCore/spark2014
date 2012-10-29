package body The_Stack_Model
--# own State is S, Pointer; -- Refinement constituents
is
   Max_Stack_Size : constant := 1024;
   type Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range is Pointer_Range
   range 1 .. Max_Stack_Size;
   type Vector is array (Index_Range) of Integer;

   S: Vector;                              -- Declaration of constituents
   Pointer: Pointer_Range;

   -- The following proof functions provide notional coversion to and from the
   --  abstract own variable to its constituents.
   --# function Model_Stack (P : Pointer_Range; V : Vector) return Stack;
   --# function Model_Pointer (S : Stack) return Pointer_Range;
   --# function Model_Vector (S : Stack) return Vector;

   -- The refinement of the proof functions Head and Tail
   --# function Head (S : Stack) return Integer;
   --# return  Model_Vector (S) (Model_Pointer (S));

   --# function Tail (S : Stack) return Stack;
   --# return Model_Stack (Model_Pointer (S) - 1, Model_Vector (S));

   -- The proof functions Head, Tail, Is_Empty and Is_Full all need user defined
   -- rules as we cannot use the functions directly in the refined
   -- proof contracts as they are defined the notional type of the own variable.
   -- The following rules are required:
   --  stack(3): not the_stack_model__is_empty(State) may_be_replaced_by fld_pointer(State) <> 0 .
   --  stack(4): not the_stack_model__is_full(State) may_be_replaced_by fld_pointer(State) < max_stack_size .
   --
   --  stack(7): head(State) may_be_replaced_by element(fld_s(State), [fld_pointer(State)]) .
   --  stack(8): head(Final_State) may_be_replaced_by X
   --               if [not the_stack_model__is_empty(Initial_State),
   --                  fld_pointer(Final_State) = fld_pointer(Initial_State),
   --                  Initial_S = fld_s(Initial_State),
   --                  fld_s(Final_State) = update(Initial_S, [fld_pointer(Initial_State)], X) ] .
   --  stack(9): head(Final_State) may_be_replaced_by X
   --               if [not the_stack_model__is_full(Initial_State),
   --                  Initial_S = fld_s(Initial_State),
   --                  fld_s(Final_State) = update(Initial_S, [fld_pointer(Final_State)], X) ] .
   --  stack(10): tail(Final_State) may_be_replaced_by tail(Initial_State)
   --               if [not the_stack_model__is_empty(Initial_State),
   --                  fld_pointer(Final_State) = fld_pointer(Initial_State),
   --                  Initial_S = fld_s(Initial_State),
   --                  fld_s(Final_State) = update(Initial_S, [fld_pointer(Initial_State)], _) ] .
   --  stack(11): tail(Final_State) may_be_replaced_by Initial_State
   --               if [not the_stack_model__is_full(Initial_State),
   --                  fld_pointer(Final_State) = fld_pointer(Initial_State) + 1,
   --                  Initial_S = fld_s(Initial_State),
   --                  fld_s(Final_State) = update(Initial_S, [fld_pointer(Final_State)], _) ] .
   --  stack(12): tail(Initial_State) may_be_replaced_by Final_State
   --               if [not the_stack_model__is_empty(Initial_State),
   --                  Initial_Pointer = fld_pointer(Initial_State),
   --                  fld_pointer(Final_State) = Initial_Pointer - 1] .

   function Is_Empty  return Boolean       -- Proof and Ada functions
   --# global Pointer;                     -- refined in terms of constituents
   --# return Pointer = 0;                 -- refined post condition
   is
   begin
      return Pointer = 0;
   end Is_Empty;

   function Is_Full  return Boolean
   --# global Pointer;
   --# return Pointer = Max_Stack_Size;
   is
   begin
      return Pointer = Max_Stack_Size;
   end Is_Full;


   function Top return Integer
   --# global Pointer, S;
   --# pre Pointer /= 0;                   -- The refined pre and postconditions
   --# return S (Pointer);                 -- cannot use the abstract pre and
   is                                      -- post conditions as they are declared
   begin                                   -- in terms of the notional type of
      return S (Pointer);                  -- the own variable.
   end Top;


   procedure Push(X: in Integer)
   --# global in out S, Pointer;
   --# pre Pointer < Max_Stack_Size;
   --# post Pointer = Pointer~ + 1 and S = S~[Pointer => X];
   is
   begin
      Pointer := Pointer + 1;
      S (Pointer) := X;
   end Push;

   procedure Pop(X: out Integer)
   --# global in     S;
   --#        in out Pointer;
   --# pre Pointer /= 0;
   --# post X       = S (Pointer~) and
   --#      Pointer = Pointer~ - 1;
   is
   begin
      X := S (Pointer);
      Pointer := Pointer - 1;
   end Pop;

   procedure Swap (X: in Integer)
   --# global in     Pointer;
   --#        in out S;
   --# pre pointer /= 0;
   --# post S = S~[Pointer => X];
   is
   begin
      S (Pointer) := X;
   end Swap;

begin -- Initialization - we promised to initialize the state
  Pointer := 0;
  S := Vector'(Index_Range => 0);
end The_Stack_Model;
