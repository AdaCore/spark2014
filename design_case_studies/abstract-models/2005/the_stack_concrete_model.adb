package body The_Stack_Concrete_Model
--# own State is S, Pointer; -- Refinement constituents
is
   Max_Stack_Size : constant := 1024;
   type Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range is Pointer_Range
   range 1 .. Max_Stack_Size;
   type Vector is array (Index_Range) of Integer;

   S : Vector;                              -- Declaration of constituents
   Pointer : Pointer_Range;

   -- The proof functions Head, Tail, Is_Empty and Is_Full all need user defined
   -- rules as we cannot use the functions directly in the refined
   -- proof contracts as they are defined the notional type of the own variable.
   -- Worse still we have to give the rules for Is_Empty and Is_Full for
   -- both local and exteranal visibility.
   -- The following rules are required:
   --  stack(1): not is_empty(State) may_be_replaced_by fld_pointer(State) <> 0 .
   --  stack(2): not is_full(State) may_be_replaced_by fld_pointer(State) < max_stack_size .
   --  stack(3): not the_stack_concrete_model__is_empty(State) may_be_replaced_by fld_pointer(State) <> 0 .
   --  stack(4): not the_stack_concrete_model__is_full(State) may_be_replaced_by fld_pointer(State) < max_stack_size .
   --
   --  stack(7): the_stack_concrete_model__head(State)
   --            may_be_replaced_by element(fld_s(State), [fld_pointer(State)]) .
   --
   --  stack(8): the_stack_concrete_model__head(Final_State) may_be_replaced_by X
   --               if [not the_stack_concrete_model__is_empty(Initial_State),
   --                  fld_pointer(Final_State) = fld_pointer(Initial_State),
   --                  Initial_S = fld_s(Initial_State),
   --                  fld_s(Final_State) = update(Initial_S, [fld_pointer(Initial_State)], X) ] .
   --  stack(9): the_stack_concrete_model__head(Final_State) may_be_replaced_by X
   --               if [not the_stack_concrete_model__is_full(Initial_State),
   --                  Initial_S = fld_s(Initial_State),
   --                  fld_s(Final_State) = update(Initial_S, [fld_pointer(Final_State)], X) ] .
   --  stack(10): the_stack_concrete_model__tail(Final_State)
   --                  may_be_replaced_by
   --             the_stack_concrete_model__tail(Initial_State)
   --               if [not the_stack_concrete_model__is_empty(Initial_State),
   --                  fld_pointer(Final_State) = fld_pointer(Initial_State),
   --                  Initial_S = fld_s(Initial_State),
   --                  fld_s(Final_State) = update(Initial_S, [fld_pointer(Initial_State)], _) ] .
   --  stack(11): the_stack_concrete_model__tail(Final_State)
   --                  may_be_replaced_by the_stack_concrete_model__to_model(Initial_State)
   --               if [not the_stack_concrete_model__is_full(Initial_State),
   --                  fld_pointer(Final_State) = fld_pointer(Initial_State) + 1,
   --                  Initial_S = fld_s(Initial_State),
   --                  fld_s(Final_State) = update(Initial_S, [fld_pointer(Final_State)], _) ] .
   --  stack(12): the_stack_concrete_model__tail(Initial_State)
   --                  may_be_replaced_by the_stack_concrete_model__to_model(Final_State)
   --               if [not the_stack_concrete_model__is_empty(Initial_State),
   --                  Initial_Pointer = fld_pointer(Initial_State),
   --                  fld_pointer(Final_State) = Initial_Pointer - 1] .

   function To_Model return Stack_Model
   --# global Pointer;
   is
   begin
      return Stack_Model'(Value => Natural (Pointer));
   end To_Model;


   function Head return Integer
   --# global Pointer, S;
   --# pre Pointer /= 0;
   --# return S (Pointer);
   is
   begin
      return S (Pointer);
   end Head;

   function Tail return Stack_Model
   --# global Pointer;
   --# pre Pointer /= 0;
   --# return Stack_Model'(Value => Natural (Pointer - 1));
   is
   begin
      return Stack_Model'(Value => Natural (Pointer - 1));
   end Tail;

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
end The_Stack_Concrete_Model;
