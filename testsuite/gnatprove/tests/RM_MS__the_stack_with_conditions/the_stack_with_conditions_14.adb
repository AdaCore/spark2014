-- In the package body the state refinement contract defines the
--  constituents of the state abstraction "State". The global (and
--  derives, if present) contracts are refined in terms of these
--  constituents. The postconditions of Is_Empty and Is_Full have to
--  be refined in terms of the state abstraction constituents.  As the
--  bodies of Push, Pop, Top and Swap are in the body of the package
--  the refined view of the postconditions of Is_Empty and Is_Full are
--  visible and so no refinement of Push, Pop, Top and Swap
--  preconditions are required. There are no refinement checks
--  required. This implementation has executable contracts , but an
--  open question is: should refined pre and postconditions be
--  executed when they are visible? In this simple example the refined
--  postconditions for Is_Empty and Is_Full could just be replaced by
--  function expressions which are both a refined postcondition and an
--  implementation.

package body the_stack_with_conditions_14
  with SPARK_Mode,
       Refined_State => (State => (S, Pointer)) -- State refinement
is
   Max_Stack_Size : constant := 1024;
   type    Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range is Pointer_Range range 1 .. Max_Stack_Size;
   type    Vector is array (Index_Range) of Integer;

   -- Declaration of constituents
   S       : Vector;
   Pointer : Pointer_Range;

   --  The subprogram contracts are refined in terms of the
   --  constituents. Expression functions could be used where
   --  applicable.

   function Is_Empty return Boolean is (Pointer = 0)
     with Refined_Global => Pointer,
          Refined_Post   => Is_Empty'Result = (Pointer = 0);

   function Is_Full return Boolean is (Pointer = Max_Stack_Size)
     with Refined_Global => Pointer,
          Refined_Post   => Is_Full'Result = (Pointer = Max_Stack_Size);

   function Top return Integer is (S (Pointer))
     with Refined_Global => (Pointer, S);

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
     with Refined_Global => (Input  => Pointer,
                             In_Out => S)
   is
   begin
      S (Pointer) := X;
   end Swap;

begin
   -- Initialization - we promised to initialize the state
   Pointer := 0;
   S := Vector'(Index_Range => 0);
end the_stack_with_conditions_14;
