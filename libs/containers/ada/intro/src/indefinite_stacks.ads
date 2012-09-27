with Ada.Unchecked_Deallocation;
generic
   type Item_Type is private;

package Indefinite_Stacks is

   --  A stack package that holds any kind of objects

   type Content_Ref is access all Item_Type;

   --  Pointer to the Content Element

   type Stack;
   type Stack_Ptr is  access all Stack;

   type Stack is record
      Element : Content_Ref;

      --  Points to the content element

      Previous : Stack_Ptr;

      --  Points to the next element cell

      Next : Stack_Ptr;

      --  Points to the next element cell
   end record;

   function Create (Default : Content_Ref)
                    return Stack_Ptr;

   --  Create stack with I elements

   function Is_Empty (S : Stack_Ptr) return Boolean;

   function Peek (S : Stack_Ptr) return Content_Ref
   with Pre => not Is_Empty (S);

   --  Returns  the topmost element of the stack without removing it

   function Push (S : Stack_Ptr; X : Content_Ref) return Stack_Ptr with
     Post => not Is_Empty (Push'Result)
       and then Peek (Push'Result) = X;

   --  Leave the current stack alone and
   --  Returns  a new stack with the new element on top
   --  Note that "S" is an "in" parameter and is not modified. So Push
   --  Make a copy of S, modify the copy, and then return that modified copy.

   procedure Push (S : in out Stack_Ptr; X : Content_Ref)
   with Post => ((not Is_Empty (S))
   and then (Peek (S) = X));

   --  Push a new element on the stack

   function Pop (S : in out Stack_Ptr) return Content_Ref  with
     Pre  => not Is_Empty (S),
     Post => Pop'Result = Peek (S)'Old;

   --  Same as the above procedure, but return the topmost element,
   --  Instead of having an out parameter
   --  Note that only in Ada 2012 functions can have in out parameters.

   procedure Pop (S : in out Stack_Ptr; X : out Content_Ref) with
     Pre  => not Is_Empty (S),
     Post => X = Peek (S)'Old;

   --  Remove the topmost element from the stack, and return it in X

private
   procedure Free_Stack is new Ada.Unchecked_Deallocation
     (Object => Item_Type,
      Name => Content_Ref);
end Indefinite_Stacks;
