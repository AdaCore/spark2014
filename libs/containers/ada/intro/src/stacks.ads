generic
   type Element is private;

   Default_Value : Element;
   --  Value used to initialize not used stack elements;

package Stacks is

   Default_Size  : constant := 1_000;

   type Content_Type is array (Integer range <>) of Element;

   --  The array that holds the elements

   type Stack (Size : Positive) is record
      Content : Content_Type (1 .. Size);
      Index   : Integer;

      --  Points to the first empty cell

   end record;

   function Create (I : Positive := Default_Size) return Stack;

   --  Create stack with I elements

   function Is_Empty (S : Stack) return Boolean;

   function Is_Full (S : Stack) return Boolean;

   function Peek (S : Stack) return Element with
     Pre => not Is_Empty (S);

   --  Returns  the topmost element of the stack without removing it

   function Push (S : Stack; X : Element) return Stack with
     Pre  => not Is_Full (S),
     Post => not Is_Empty (Push'Result)
       and then Peek (Push'Result) = X;

   --  Leave the current stack alone and
   --  Returns  a new stack with the new element on top
   --  Note that "S" is an "in" parameter and is not modified. So Push
   --  Make a copy of S, modify the copy, and then return that modified copy.

   procedure Push (S : in out Stack; X : Element) with
     Pre  => not Is_Full (S),
     Post => S = Push (S'Old, X);

   --  Push a new element on the stack

   function Pop (S : in out Stack) return Element with
     Pre  => not Is_Empty (S),
     Post => not Is_Full (S)
               and then Pop'Result = Peek (S)'Old;

   --  Same as the above procedure, but return the topmost element,
   --  Istead of having an out parameter
   --  Note that only in Ada 2012 functions can have in out parameters.

   procedure Pop (S : in out Stack; X : out Element) with
     Pre  => not Is_Empty (S),
     Post => not Is_Full (S)
               and then X = Peek (S)'Old;

   --  Remove the topmost element from the stack, and return it in X

end Stacks;
