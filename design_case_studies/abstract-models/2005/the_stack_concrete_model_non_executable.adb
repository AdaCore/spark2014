package body The_Stack_Concrete_Model_non_Executable
--# own State is S, Pointer; -- Refinement constituents
is
   Max_Stack_Size : constant := 1024;
   type Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range is Pointer_Range
   range 1 .. Max_Stack_Size;
   type Vector is array (Index_Range) of Integer;

   S: Vector;                              -- Declaration of constituents
   Pointer: Pointer_Range;

   -- The proof functions Head, Tail, To_Model, Is_Empty and Is_Full all
   -- need user defined rules as we cannot use the functions directly in the refined
   -- proof contracts as they are defined the notional type of the own variable.
   -- The following rules are required:
   --  stack(3): not the_stack_concrete_model_non_executable__is_empty(State)
   --            may_be_replaced_by fld_pointer(State) <> 0 .
   --  stack(4): not the_stack_concrete_model_non_executable__is_full(State)
   --            may_be_replaced_by fld_pointer(State) < max_stack_size .
   --
   --  stack(5): to_model(Final_State) may_be_replaced_by tail(Initial_State)
   --            if [fld_s(Initial_State) = fld_s(Final_State),
   --                Initial_Pointer = fld_pointer(Initial_State),
   --                fld_pointer(Final_State) = Initial_Pointer - 1] .
   --
   --  stack(6): to_model(Initial_State) may_be_replaced_by tail(Final_State)
   --             if [Initial_S = fld_s(Initial_State),
   --                 Initial_Pointer = fld_pointer(Initial_State),
   --                 fld_s(Final_State) = update(Initial_S, [fld_pointer(Final_State)], _),
   --                 fld_pointer(Final_State) = Initial_Pointer + 1] .
   --
   --  stack(8): head(State) may_be_replaced_by element(fld_s(State), [fld_pointer(State)]) .
   --
   --  stack(9): head(Final_State) may_be_replaced_by X
   --            if [not the_stack_concrete_model_non_executable__is_full(Initial_State),
   --                Initial_S = fld_s(Initial_State),
   --                Initial_Pointer = fld_pointer(Initial_State),
   --                fld_s(Final_State) = update(Initial_S, [fld_pointer(Final_State)], X),
   --                fld_pointer(Final_State) = Initial_Pointer + 1] .
   --
   --  stack(10): head(Final_State) may_be_replaced_by X
   --             if [fld_pointer(Initial_State) = fld_pointer(Final_State),
   --                 Initial_S = fld_s(Initial_State),
   --                 fld_s(Final_State) = update(Initial_S, [fld_pointer(Initial_State)], X)] .
   --
   --  stack(12): tail(Final_State) may_be_replaced_by tail(Initial_State)
   --             if [fld_pointer(Initial_State) = fld_pointer(Final_State),
   --                 Initial_S = fld_s(Initial_State),
   --                 fld_s(Final_State) = update(Initial_S, [fld_pointer(Initial_State)], _)] .

   -- The following proof functions provide notional coversion to and from the
   --  abstract own variable to its constituents.
   --# function State_Pointer (S : Stack) return Pointer_Range;
   --# function State_Vector (S : Stack) return Vector;
   --# function To_Model_From_Parts (V : Vector; P : Pointer_Range) return Stack_Model;

   --# function To_Model (The_Stack : Stack) return Stack_Model;
   --# return Stack_Model'(Value => Natural (State_Pointer (The_Stack)));

   --# function Head (The_Stack : Stack) return Integer;
   --# return State_Vector (The_Stack) (State_Pointer (The_Stack));

   --# function Tail (The_Stack : Stack) return Stack_Model;
   --# return To_Model_From_Parts (State_Vector (The_Stack), State_Pointer (The_Stack) - 1);

   function Is_Empty  return Boolean       -- Proof and Ada functions
   --# global Pointer;                     -- refined in terms of constituents
   --# return Pointer = 0;
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
   --# pre Pointer /= 0;
   --# return S (Pointer);
   is
   begin
      return S (Pointer);
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
   --# post  X = S (Pointer~) and
   --#       Pointer = Pointer~ - 1;
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
end The_Stack_Concrete_Model_Non_Executable;
