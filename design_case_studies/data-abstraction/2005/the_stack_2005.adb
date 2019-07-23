-- In the package body the own variable refinement annotation defines its
-- constituents, that is, the state items which make up the abstraction.
-- The global (and derives, if present) annotations have to be refined in terms
-- ot the constituents of the own variable abstraction.
-- The subprograms in this package body cannot be shown to be free of RTE
-- without more defensive programming or incorporating preconditions.
package body The_Stack_2005
--# own State is S, Pointer; -- Refinement constituents
is
   Max_Stack_Size : constant := 1024;
   type Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range is Pointer_Range
   range 1 .. Max_Stack_Size;
   type Vector is array (Index_Range) of Integer;

   S: Vector;                              -- Declaration of constituents
   Pointer: Pointer_Range;

   function Is_Empty  return Boolean
   --# global Pointer;                     -- refined in terms of constituents
   is
   begin
      return Pointer = 0;
   end Is_Empty;

   function Is_Full  return Boolean
   --# global Pointer;                     -- refined in terms of constituents
   is
   begin
      return Pointer = Max_Stack_Size;
   end Is_Full;


   procedure Push(X: in Integer)
   --# global in out S, Pointer;           -- refined in terms of constituents
   is
   begin
      Pointer := Pointer + 1;
      S (Pointer) := X;
   end Push;

   procedure Pop(X: out Integer)
   --# global in out Pointer;              -- refined in terms of constituents
   --#        in     S;
   is
   begin
      X := S (Pointer);
      Pointer := Pointer - 1;
   end Pop;

   procedure Swap (X: in Integer)
   --# global in     Pointer;
   --#        in out S;
   is
   begin
      S (Pointer) := X;
   end Swap;

begin -- Initialization - we promised to initialize the state
  Pointer := 0;
  S := Vector'(Index_Range => 0);
end The_Stack_2005;
