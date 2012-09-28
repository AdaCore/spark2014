with Ada.Unchecked_Deallocation;
package Unbounded_Integer_Stacks is

   --  A stack package that holds integers

   Chunk_Size : constant Positive := 2;

   --  The number of elements in a stack

   Default_Value : constant Integer := -1;

   --  Value used to initialize not used stack elements;

   type Content_Type  is array (Natural range <>) of Integer;

   --  The array that holds the elements

   type Content_Ref is access Content_Type;

   --  Pointer to array

   type Stack (Size : Positive) is record
      Cont_Ptr : Content_Ref := new Content_Type (1 .. Size);

      --  Points to the content array

      Index   : Natural;

      --  Points to the first empty cell

   end record;

   type Stack_Ptr is access all Stack;

   function Create return Stack;

   --  Create Stack with I elements

   function Is_Empty (S : Stack) return Boolean;

   function Is_Full (S : Stack) return Boolean;

   function Peek (S : Stack) return Integer
   with Pre => not Is_Empty (S);

   --  Returns  the topmost element of the stack without removing it

   function Pop (S : in out Stack) return Integer with
     Pre  => not Is_Empty (S),
   Post => not Is_Full (S)
     and then Pop'Result = Peek (S)'Old;

   --  Same as the above procedure, but return the topmost element,
   --  Instead of having an out parameter
   --  Note that only in Ada 2012 functions can have in out parameters.

   procedure Pop (S : in out Stack; X : out Integer) with
     Pre  => not Is_Empty (S),
     Post => not Is_Full (S)
               and then Peek (S)'Old = X;

   --  Remove the topmost element from the stack, and return it in X

   function Push (S : Stack; X : Integer) return Stack with
     Post => not Is_Empty (Push'Result)
     and then Peek (Push'Result) = X;

   --  Leave the current stack alone and
   --  Returns  a new stack with the new element on top
   --  Note that "S" is an "in" parameter and is not modified. So Push
   --  Make a copy of S, modify the copy, and then return that modified copy.

   procedure Push (S : in out Stack; X : Integer) with
     Post => not Is_Empty (S);
   --  and then Push (S'Old, X) = S;

   --  Push a new element on the stack
private

   procedure Enlarge (S : in out Stack) with
     Post => (not Is_Full (S));

   --  Enlarge the stack

   procedure Free_Content is new Ada.Unchecked_Deallocation
     (Object => Content_Type,
      Name => Content_Ref);
end Unbounded_Integer_Stacks;
