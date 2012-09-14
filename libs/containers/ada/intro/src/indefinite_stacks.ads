
generic
   type Item_Type is private;

package Indefinite_Stacks is
   --  A stack package that holds integers

   Chunk_Size                      : constant Positive := 100;
   --  the number of elements in a stack
   Default_Value                   : Item_Type;
   --  value used to initialize not used stack elements;

   type Content_Type is array (Natural range <>) of Item_Type;
   --  the array that holds the elements

   type Content_Ref is access Content_Type;
   --  pointer to array

   type Stack (Size                : Positive) is record
      Cont_Ptr                     : Content_Ref := new Content_Type (1 .. Size);
      --  points to the content array
      Index                        : Natural;
      --  points to the first empty cell
   end record;

   type Stack_Ptr is access all Stack;

   function Create (I              : Positive := Chunk_Size; Default : Item_Type) return Stack;
   -- Create stack with I elements

   function Is_Empty (S            : Stack) return Boolean;

   function Is_Full (S             : Stack) return Boolean;

   procedure Push (S               : in out Stack; X : Item_Type)
   with Pre => (not Is_Full (S)
               ),
   Post => ((not Is_Empty (S))
            and ( Peek (S) = X )   --from (8
           );
   --  push a new element on the stack

   procedure Pop (S                : in out Stack; X : out Item_Type)
   with Pre => (not Is_Empty (S) ),
   Post => (not Is_Full (S));
   --  remove the topmost element from the stack, and return it in X

   function Pop (S                 : in out Stack) return Item_Type
   --  with Post => Pop'Result = Peek (S'Old)
   ;
   --  same as the above procedure, but return the topmost element,
   --  instead of having an out parameter
   --  note that only in Ada 2012 functions can have in out parameters.

   function Peek (S                : Stack) return Item_Type;
   --  returns  the topmost element of the stack without removing it

   function Push (S                : Stack; X : Item_Type) return Stack;
   --  leave the current stack alone and
   --  returns  a new stack with the new element on top
   --  Note that "S" is an "in" parameter and is not modified. So Push
   --  make a copy of S, modify the copy, and then return that modified copy.

   procedure test_Pop_When_Empty(S : in out Stack);
   -- test pop assertion
   -- this should be raised when the stack is empty
private

   procedure Enlarge ( S           : in out Stack;
                      Delta_Size   : Positive := Chunk_Size)
   with  Post => (not Is_Full (S)  );

end Indefinite_Stacks;

