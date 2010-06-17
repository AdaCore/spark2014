with Ada.Containers.Doubly_Linked_Lists; use Ada.Containers;

package Tests is

   type Elem is new Integer;
   package My_Lists is new Ada.Containers.Doubly_Linked_Lists (Elem);
   use My_Lists;

   --  Removing an element from a list decreases its length by one
   procedure Test1 (Li : in out List; C : in out Cursor);
   pragma Precondition (Has_Element (C));
   pragma Postcondition (Length (Li) = Length (Li)'Old - 1);

   --  Take a list of 4 elements, prepend element E, remove all initial 4
   --  elements and take the last element of the list, it is E
   procedure Test2 (Li : in out List; E : Elem; Result : out Elem);
   pragma Precondition (Length (Li) = 4);
   pragma Postcondition (Result = E);

   --  Adding elements to a list does not invalidate an existing cursor
   procedure Test3 (Li : in out List; C,D,F,G,H : Cursor; E : Elem);
   pragma Precondition ( --  It is not possible to get the position of
                         --  a Cursor with Ada containers, so ignore the
                         --  precondition "Position (C) = 4" for now, and
                         --  replace it with the following equality test
                        C = Next (Next (Next (First (Li))))
                        and Has_Element (F) and Has_Element (H));
   pragma Postcondition (Has_Element (C));

   --  Iterate through the list and increment a counter, which should equal
   --  the length of the list on exit
   function Test4 (Li : List) return Count_Type;
   pragma Postcondition (Test4'Result = Length (Li));

   --  Iterate through the list by adding element E at every position.
   --  This doubles the size of the list.
   procedure Test5 (Li : in out List; E : Elem);
   pragma Precondition (not Is_Empty (Li));
   pragma Postcondition (Length (Li) = 2 * Length (Li)'Old);

end Tests;
