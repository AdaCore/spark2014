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
package body the_stack_with_conditions_05
--# own State is S, Pointer; -- Refinement constituents
is
   Max_Stack_Size : constant := 1024;
   type Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range is Pointer_Range
   range 1 .. Max_Stack_Size;
   type Vector is array (Index_Range) of Integer;

   S: Vector;                              -- Declaration of constituents
   Pointer: Pointer_Range;

   function Is_Empty return Boolean       -- Proof and Ada functions
   --# global Pointer;                     -- refined in terms of constituents
   --# return Pointer = 0;
   is
   begin
      return Pointer = 0;
   end Is_Empty;

   function Is_Full return Boolean
   --# global Pointer;
   --# return Pointer = Max_Stack_Size;
   is
   begin
      return Pointer = Max_Stack_Size;
   end Is_Full;


   function Top return Integer
   --# global Pointer, S;
   --# pre not Is_Empty (Pointer);
   --# return S (Pointer);
   is
   begin
      return S (Pointer);
   end Top;


   procedure Push(X: in Integer)
   --# global in out S, Pointer;
   --# pre not Is_Full (Pointer);
   is
   begin
      Pointer := Pointer + 1;
      S (Pointer) := X;
   end Push;

   procedure Pop(X: out Integer)
   --# global in     S;
   --#        in out Pointer;
   --# pre not Is_Empty (Pointer);
   is
   begin
      X := S (Pointer);
      Pointer := Pointer - 1;
   end Pop;

   procedure Swap (X: in Integer)
   --# global in     Pointer;
   --#        in out S;
   --# pre not Is_Empty (Pointer);
   is
   begin
      S (Pointer) := X;
   end Swap;

begin -- Initialization - we promised to initialize the state
  Pointer := 0;
  S := Vector'(Index_Range => 0);
end the_stack_with_conditions_05;
