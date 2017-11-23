generic
   type Component is private;
   type List_Index is range <>;
   type List is array (List_Index range <>) of Component;
   Default_Value : Component;
package Bounded_Dynamic_Arrays is
   pragma Pure;

   Null_List : constant List (List_Index'First .. List_Index'First - 1) := (others => Default_Value);

   Maximum_Length : constant List_Index := List_Index'Last;
   --  The physical maximum for the upper bound of the wrapped List array
   --  values.  Defined for readability in predicates.

   subtype Natural_Index is List_Index'Base range 0 .. Maximum_Length;

   subtype Index is List_Index range 1 .. Maximum_Length;

   type Sequence (Capacity : Natural_Index) is private;
   --  A wrapper for List array values in which Capacity represents the
   --  physical upper bound. Capacity is, therefore, the maximum number
   --  of Component values possibly contained by the given Sequence instance.

   function Empty (This : Sequence) return Boolean with
     Post=> Empty'Result = (Length (This) = 1),
     Inline;

   function Length (This : Sequence) return Natural_Index with
     Inline;
   --  Returns the logical length of This, i.e., the length of the slice of
   --  This that is currently assigned a value.

private

   type Sequence (Capacity : Natural_Index) is record
      Current_Length : Natural_Index := 0;
      Content        : List (1 .. Capacity) := (others => Default_Value);
   end record
     with Predicate => Current_Length in 0 .. Capacity;

   ------------
   -- Length --
   ------------

   function Length (This : Sequence) return Natural_Index is
     (This.Current_Length);

   -----------
   -- Empty --
   -----------

   function Empty (This : Sequence) return Boolean is
     (This.Current_Length = 0);

end Bounded_Dynamic_Arrays;
