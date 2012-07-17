-- In the package body the own variable is refined in to its constituent parts
-- and the global and derives annotations refined in terms of these constituents.
-- The return annotations of Is_Empty and Is_Full have to be refined in terms
-- of the abstract own variable constituents.
-- The implicitly defined functions representing Is_Empty and Is_Full cannot
-- be used or applied inside the body as they are in terms of the
-- abstract own variable "State".
-- Instead, we have to specify refined pre conditions to Push, Pop, Top and Swap.
-- This leads to the requirement to show that their preconditions given in the
-- package specification implies their refined preconditions given in the body.
-- The proof obligations resulting from these refinement checks cannot be discharged
-- without the introduction of user defined proof functions given in
-- comments in the text.
package body The_Stack_With_Conditions_2005
--# own State is S, Pointer; -- Refinement constituents
is
   Max_Stack_Size : constant := 1024;
   type Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range is Pointer_Range
   range 1 .. Max_Stack_Size;
   type Vector is array (Index_Range) of Integer;

   S: Vector;                              -- Declaration of constituents
   Pointer: Pointer_Range;

   -- The functions have to be defined by user rules
   -- to prove the refinement checks
   -- stack(1): not the_stack_2__is_empty(State) may_be_replaced_by fld_pointer(State) <> 0 .
   -- stack(2): not the_stack_2__is_full(State) may_be_replaced_by fld_pointer(State) < max_stack_size .

   -- The meaning of State = State~ has also defined in a user rule
   -- stack(3): the_stack_2__top(Initial_State) = x -> Final_State = Initial_State may_be_deduced_from
   --        [ fld_pointer(Initial_State) = fld_pointer(Final_State) ] .

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
   is
   begin
      Pointer := Pointer + 1;
      S (Pointer) := X;
   end Push;

   procedure Pop(X: out Integer)
   --# global in     S;
   --#        in out Pointer;
   --# pre Pointer /= 0;
   is
   begin
      X := S (Pointer);
      Pointer := Pointer - 1;
   end Pop;

   procedure Swap (X: in Integer)
   --# global in     Pointer;
   --#        in out S;
   --# pre pointer /= 0;
   is
   begin
      S (Pointer) := X;
   end Swap;

begin -- Initialization - we promised to initialize the state
  Pointer := 0;
  S := Vector'(Index_Range => 0);
end The_Stack_With_Conditions_2005;
