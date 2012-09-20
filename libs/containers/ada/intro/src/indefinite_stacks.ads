generic
   type Item_Type is private;

package Indefinite_Stacks is

   --  A stack package that holds integers

   type Content_Ref is access Item_Type;

   -- Pointer to the Content Element

   type Stack;
   type Stack_Ptr is access all Stack;

   type Stack (Object  : Content_Ref) is record
      Element : Content_Ref := Object;

      --  Points to the content element

      Next : Stack_Ptr;

      --  Points to the next element cell

   end record;

   function Create (Default : Item_Type)
                    return Stack;

   --  Create stack with I elements

   function Is_Empty (S : Stack_Ptr) return Boolean;

   procedure Push (S : in out Stack_Ptr; X : Item_Type)
   with Post => ((not Is_Empty (S)) and (Peek (S) = X));

   --  Push a new element on the stack

   procedure Pop (S : in out Stack_Ptr; X : out Item_Type)
   with Pre => (not Is_Empty (S));

   --  Remove the topmost element from the stack, and return it in X

   function Pop (S : in out Stack_Ptr) return Item_Type;

   --  Same as the above procedure, but return the topmost element,
   --  Instead of having an out parameter
   --  Note that only in Ada 2012 functions can have in out parameters.

   function Peek (S : Stack_Ptr) return Item_Type;

   --  Returns  the topmost element of the stack without removing it

   function Push (S : Stack; X : Item_Type) return Stack;

   --  Leave the current stack alone and
   --  Returns  a new stack with the new element on top
   --  Note that "S" is an "in" parameter and is not modified. So Push
   --  Make a copy of S, modify the copy, and then return that modified copy.

   procedure test_Pop_When_Empty (S : in out Stack_Ptr);

   --  Test pop assertion
   --  This should be raised when the stack is empty

private

end Indefinite_Stacks;
