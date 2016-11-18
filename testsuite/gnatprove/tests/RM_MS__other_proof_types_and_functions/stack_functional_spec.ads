pragma Unevaluated_Use_Of_Old(Allow);
package Stack_Functional_Spec
  with SPARK_Mode,
       Abstract_State    => State,
       Initializes       => State,
       Initial_Condition => Is_Empty
is
   --  Abstract states do not have types in SPARK 2014 but to provide
   --  functional specifications it is sometimes necessary to refer to
   --  the abstract state in an assertion expression such as a post
   --  condition. To do this in SPARK 2014 an Ada type declaration is
   --  required to represent the type of the abstract state, then a
   --  function applied to the abstract state (as a global) can be
   --  written which returns an object of the declared type.
   type Stack_Type is private;

   --  The Abstract_State name may be overloaded by the function which
   --  represents it in assertion expressions.
   function State return Stack_Type
     with Global => State;

   function Max_Stack_Size return Natural
     with Ghost;

   --  Returns the number of elements on the stack
   --  A function may have a formal parameter (or return a value)
   --  of the abstract state.
   function Count (S : Stack_Type) return Natural
     with Ghost;

   -- Returns the Nth entry on the stack.
   -- Stack_Entry (S, Count (S)) is the top of stack
   function Stack_Entry (S : Stack_Type; N : Natural) return Integer
     with Pre        => N in 1 .. Count (S),
          Ghost;

   -- The ghost function Count can be called in the function
   -- expression because Is_Empty is also a ghost function.
   function Is_Empty return Boolean is (Count (State) = 0)
     with Global     => State,
          Ghost;

   function Is_Full return Boolean is (Count(State) = Max_Stack_Size)
     with Global     => State,
          Ghost;

   --  The precondition requires the stack is not full when a value, X,
   --  is pushed onto it.
   --  Functions with global items (Is_Full with global State in this case)
   --  can be called in an assertion expression such as the precondition here.
   --  The postcondition indicates that the count of the stack will be
   --  incremented after a push and therefore the stack will be non-empty.
   --  The item X is now the top of the stack and the contents of the rest of
   --  the stack are unchanged.
   procedure Push (X : in Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Full,
          Post   => Count (State) = Count (State'Old) + 1 and
                    Count (State) <= Max_Stack_Size and
                    Stack_Entry (State, Count (State)) = X and
                    (for all I in 1 .. Count (State'Old) =>
                        Stack_Entry (State, I) = Stack_Entry (State'Old, I));

   --  The precondition requires the stack is not empty when we
   --  pull a value from it.
   --  The postcondition indicates that the X = the old top of stack,
   --  the stack count is decremented, and the contents of the stack excluding
   --  the old top of stack are unchanged.
   procedure Pop (X : out Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Empty,
          Post   => Count (State) = Count (State'Old) - 1 and
                    X = Stack_Entry (State'Old, Count (State'Old)) and
                   (for all I in 1 .. Count (State) =>
                       Stack_Entry (State, I) = Stack_Entry (State'Old, I));

   --  The precondition requires that the stack has at least 2 entries
   --  (Count >= 2).
   --  The postcondition states that the top two elements of the stack are
   --  transposed but the remainder of the stack is unchanged.
   procedure Swap2
     with Global => (In_Out => State),
          Pre    => Count (State) >= 2,
          Post   => Count(State) = Count (State'Old) and
                    Stack_Entry (State, Count (State)) =
                       Stack_Entry (State'Old, Count (State) - 1) and
                    Stack_Entry (State, Count (State) - 1) =
                       Stack_Entry (State'Old, Count (State)) and
                    (for all I in 1 .. Count (State) - 2 =>
                        Stack_Entry (State, I) = Stack_Entry (State'Old, I));

private
   -- The full type declarion used to represent the abstract state.
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1 .. Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   type Stack_Type is record
      S : Vector;
      Pointer : Pointer_Range;
   end record;
end Stack_Functional_Spec;
