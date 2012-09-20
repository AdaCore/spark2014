package Unbounded_Integer_Stacks is

   --  A stack package that holds integers

   Chunk_Size : constant Positive := 1000;

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

   --  Function Create return Stack;
   --  Create stack with MaxSize elements

   function Create (I : Positive := Chunk_Size) return Stack;

   --  Create Stack with I elements

   procedure Enlarge (S : in out Stack; Delta_Size : Positive := Chunk_Size)
     with Pre => (Is_Full (S)),
     Post => (not Is_Full (S));

   --  Enlarge the stack
   --  If no Delta_Size is passed it will enlarge stack by Chunk_Size

   function Is_Empty (S : Stack) return Boolean;

   function Is_Full (S : Stack) return Boolean;

   function Peek (S : Stack) return Integer
     with Pre => not Is_Empty (S);

   --  Returns  the topmost element of the stack without removing it

   function Pop (S : in out Stack) return Integer;

   --  Same as the above procedure, but return the topmost element,
   --  Instead of having an out parameter
   --  Note that only in Ada 2012 functions can have in out parameters.

   procedure Pop (S : in out Stack; X : out Integer)
     with Pre => (not Is_Empty (S)),
     Post => (not Is_Full (S));

   --  Remove the topmost element from the stack, and return it in X

   function Push (S : Stack; X : Integer) return Stack;

   --  Leave the current stack alone and
   --  Returns  a new stack with the new element on top
   --  Note that "S" is an "in" parameter and is not modified. So Push
   --  Make a copy of S, modify the copy, and then return that modified copy.

   procedure Push (S : in out Stack; X : Integer)
     with Pre => (not Is_Full (S)),
     Post => ((not Is_Empty (S)) and (Peek (S) = X));

   --  Push a new element on the stack

end Unbounded_Integer_Stacks;
