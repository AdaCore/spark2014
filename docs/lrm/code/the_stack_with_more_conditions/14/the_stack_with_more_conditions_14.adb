-- Note, in particular, the refinement of the conditional global contract of Swap.
-- The postconditions of Is_Empty and Is_Full have to be refined in terms
-- of the state abstraction constituents.
-- The postcondition of Top is refined but the postcondition of Push and Swap
-- do not be refined because they are given in terms of Top and the refined
-- postcondition of Top is visible.  There are no refinement checks required.
-- This implementation has executable contracts.
package body the_stack_with_more_conditions_14
   with Refined_State => (State => (S, Pointer)) -- State refinement
is
   Max_Stack_Size : constant := 1024;
   type Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range is Pointer_Range
   range 1 .. Max_Stack_Size;
   type Vector is array (Index_Range) of Integer;

   S: Vector;                             -- Declaration of constituents
   Pointer: Pointer_Range;

   -- The subprogram contracts are refined in terms of the constituents.
   -- Expression functions could be used where applicable

   function Is_Empty  return Boolean
      with Refined_Global => Pointer,
           Refined_Post   => Is_Empty'Result = (Pointer = 0)
   is
   begin
      return Pointer = 0;
   end Is_Empty;

   function Is_Full  return Boolean
      with Refined_Global => Pointer,
           Refined_Post   => Is_Full'Result = (Pointer = Max_Stack_Size)
   is
   begin
      return Pointer = Max_Stack_Size;
   end Is_Full;

   function Top return Integer
      with Refined_Global => (Pointer, S),
           Refined_Post   => Top'Result = S (Pointer)
   is
   begin
      return S (Pointer);
   end Top;

   procedure Push(X: in Integer)
      with Refined_Global => (In_Out => (Pointer, S))
   is
   begin
      Pointer := Pointer + 1;
      S (Pointer) := X;
   end Push;

   procedure Pop(X: out Integer)
      with Refined_Global => (Input  => S,
                              In_Out => Pointer)
   is
   begin
      X := S (Pointer);
      Pointer := Pointer - 1;
   end Pop;

   procedure Swap (X : in Integer)
      with Refined_Global => (Input  => (Pointer, S),
                              Output => (if Top /= X then S))
   is
   begin
      S (Pointer) := X;
   end Swap;
begin -- Initialization - we promised to initialize the state
   Pointer := 0;
   S := Vector'(Index_Range => 0);
end the_stack_with_more_conditions_14;
