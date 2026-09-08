package Iterable is

   type Array_Of_Integers is array (Positive range <>) of Integer;

   type Container (Max : Positive) is record
      Content : Array_Of_Integers (1 .. Max);
   end record with
     Iterable => (First       => First,
                  Has_Element => Has_Element,
                  Next        => Next,
                  Element     => Get);

   type Cursor is record
      C : Integer;
   end record;

   function First (A : Container) return Cursor;
   function Next  (A : Container; C : Cursor) return Cursor;
   function Has_Element (A : Container; C : Cursor) return Boolean;
   function Get (A : Container; C : Cursor) return Character;

end Iterable;
