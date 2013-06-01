with Ada.Unchecked_Deallocation;
with Ada.Finalization;  use Ada.Finalization;
generic
--   type Item_Type(<>) is private;
   type Item_Type is private;
package Indefinite_Stacks is

   --  A stack package that holds any kind of objects

   type Content_Ref is access all Item_Type;

   --  Pointer to the Content Element
   type Stack;
   type Stack_Ptr is  access all Stack;
   type Stack is new Controlled with record
      Element : Item_Type;

      --  Points to the content element

      Previous : Stack_Ptr;

      --  Points to the next element cell

      Next : Stack_Ptr;

      --  Points to the next element cell
   end record;

   overriding procedure Adjust (Object : in out Stack);
   overriding procedure Finalize (Object : in out Stack);

   function Create return Stack;

   --  Create stack with I elements

   function Is_Empty (S : Stack) return Boolean;

   function Peek (S : Stack) return Item_Type
   with Pre => not Is_Empty (S);

   --  Returns  the topmost element of the stack without removing it

   function Pop (S : in out Stack) return Item_Type  with
     Pre  => not Is_Empty (S),
     Post => Pop'Result = Peek (S)'Old;

   --  Same as the above procedure, but return the topmost element,
   --  Instead of having an out parameter
   --  Note that only in Ada 2012 functions can have in out parameters.

   procedure Pop (S : in out Stack; X : out Item_Type) with
     Pre  => not Is_Empty (S),
     Post => X = Peek (S)'Old;

   --  Remove the topmost element from the stack, and return it in X

   function Push (S : Stack; X : Item_Type) return Stack with
     Post => not Is_Empty (Push'Result)
       and then Peek (Push'Result) = X;

   --  Leave the current stack alone and
   --  Returns  a new stack with the new element on top
   --  Note that "S" is an "in" parameter and is not modified. So Push
   --  Make a copy of S, modify the copy, and then return that modified copy.

   procedure Push (S : in out Stack; X : Item_Type)
   with Post => ((not Is_Empty (S))
   and then Compare (S, Push (S'Old, X)));

   --  Push a new element on the stack
   function Compare (S, T : Stack) return Boolean;
private

   function Get_First (S : Stack) return Stack_Ptr;
   function Get_Last (S : Stack) return Stack_Ptr;
   procedure Free_Stack is new Ada.Unchecked_Deallocation
     (Object => Stack,
      Name => Stack_Ptr);
   procedure Free_Item is new Ada.Unchecked_Deallocation
     (Object => Item_Type,
      Name => Content_Ref);
end Indefinite_Stacks;
