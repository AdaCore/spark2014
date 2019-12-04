-- In the body the functions are so simple that function expressions are used to
-- give both a refined post condition and an implementation.
-- A refined global contract is shown for the expression functions but is
-- perhaps a little pedantic. I am not sure if we should make them
-- mandatory, optionally present or never present for the constructive profile?
-- I think optionally present is probably the most flexible with stricter
-- rules applied using GNATCheck if required.
-- The same reasoning could be applied to ordinary subprogram bodies
-- as we know from their specification the state abstraction that is global
-- and from the state refinement contract we know which globals are
-- accessible.
-- The refined postconditions using 'Update (or for all ...) are computationally
-- expensive, whereas the abstract model is computationally very cheap.
-- Perhaps it would be worth having an aspect clause denoting that the refined
-- postcondition is not to be used in the final code or to be used for proof only?
-- Having proven or demonstrated that the bodies of the subprograms satisfy the
-- constraints of the refined postcondition, just the abstract model is used.
-- That way we have an efficient model which could be retained in running code.
-- The contracts are executable.
package body The_Stack_Executable_Model
with
   Refined_State (State => (S, Pointer)) -- State refinement
is
   Max_Stack_Size : constant := 1024;
   type Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range is Pointer_Range range 1 .. Max_Stack_Size;
   type Vector is array (Index_Range) of Integer;

   S: Vector;                              -- Declaration of constituents
   Pointer: Pointer_Range;

   -- Conversion between the abstract state and the model is simple.  The
   -- Pointer is simply the result
   function Model return Stack_Model is (Stack_Model'(Value => Natural (Pointer)));

   function Is_Empty return Boolean is (Pointer = 0);

   function Is_Full return Boolean is (Pointer = Max_Stack_Size);

   -- The definition of the proof function Head is simple (the same as Top)
   function Head return Integer is (S (Pointer))

   -- The definition of the proof function Tail; not the conditional expression
   -- to make the function total so that it does not require a precondition.
   function Tail return Stack_Model is
     (Stack_Model'(Value => Natural ((if Pointer > 0 then Pointer - 1 else 0))));

   function Top return Integer is (S (Pointer));

   -- In the implementation of the procedural operations we need to ensure that
   -- the conditions for the validity of the model described in the package
   -- specification are withheld.  This is done by refining their postconditions.

   procedure Push(X: in Integer)
   with
     Refined_Global =>
       (In_Out => (Pointer, S)),
     Refined_Post =>
       Head  = X and
       Tail  = Model'Old and
       Pointer = Pointer'Old + 1 and
       S = S'Old'Update (Pointer => X)
   -- The refined post condition does introduce a proof obligation to show that
   -- the refined post condition implies the abstract postcondition but since
   -- the refined postcondition is just strengthens the condition with some
   -- extra properties the proof should be trivial.  Note that I included both
   -- Tail = Model'Old and Pointer = Pointer + 1 which is strictly not
   -- necessary as one can be derived from the other but it will make the
   -- the proof of refinement integrity easier.
   is
   begin
      Pointer := Pointer + 1;
      S (Pointer) := X;
   end Push;

   -- Here we olnly need to show that the vector of values has not changed.
   procedure Pop(X: out Integer)
   with
     Refined_Global =>
       (In_Out => (Pointer, S)),
     Refined_Post =>
       X       = Head'Old and
       Model   = Tail'Old and
       Pointer = Pointer'Old - 1 and
       S = S'Old
   -- The proof of refinement integrity should be trivial
   is
   begin
      X := S (Pointer);
      Pointer := Pointer - 1;
   end Pop;

   -- Only the top of stack is changed.
   procedure Swap (X : in Integer)
   with
     Refined_Global =>
       (Input  => Pointer,
        In_Out => S),
     Refined_Post =>
       Head = X and
       Tail = Tail'Old and
       S = S'Old'Update (Pointer => X)
   -- The proof of refinement integrity should be trivial
   is
   begin
      S (Pointer) := X;
   end Swap;


begin -- Initialization - we promised to initialize the state
  Pointer := 0;
  S := Vector'(Index_Range => 0);
end The_Stack_Executable_Model;
