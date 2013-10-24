package Stack
  with Abstract_State => State
is
   -- We have to turn the proof functions into actual functions
  function Is_Empty return Boolean
    with Global     => (Input => State),
         Convention => Ghost;

   function Is_Full return Boolean
     with Global     => (Input => State),
          Convention => Ghost;

   function Count return Natural
     with Global     => (Input => State),
          Convention => Ghost;

   --  Post-condition indicates that the stack will be
   --  non-empty after pushing an item on to it, while the pre-condition
   --  requires it is not full when we push a value onto it.
   procedure Push(X : in Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Full,
          Post   => not Is_Empty;

   --  Procedure that swaps the first two elements in a stack.
   procedure Swap2
     with Global => (In_Out => State),
          Pre    => Count >= 2,
          Post   => Count = Count'Old;

   --  Initializes the Stack.
   procedure Initialize
     with Global => (Output => State),
          Post   => Is_Empty;

private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1 .. Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   type Stack_Type is record
      S : Vector;
      Pointer : Pointer_Range;
   end record;

   Initial_Stack : constant Stack_Type :=
     Stack_Type'(S       => Vector'(others => 0),
                 Pointer => 0);
end Stack;
