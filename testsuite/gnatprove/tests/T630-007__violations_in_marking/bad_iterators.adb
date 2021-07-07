with Ada.Iterator_Interfaces;
with Ada.Containers.Formal_Doubly_Linked_Lists;
procedure Bad_Iterators with SPARK_Mode is
   type Int_Arr is array (Positive range <>) of Integer;

   type Holder is record
      C : Int_Arr (1 .. 10);
   end record;

   function Has_Element (X : Integer) return Boolean is (X in 1 .. 10);

   package Vector_Iterator_Interfaces is new
      Ada.Iterator_Interfaces (Integer, Has_Element);

   function Iterate
     (Container : Holder)
      return Vector_Iterator_Interfaces.Reversible_Iterator'Class with Import;

   package My_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Integer);

   C : Int_Arr := (1 .. 10 => 0);
   H : Holder := (C => C);
   L : My_Lists.List (15);
begin
   My_Lists.Append (L, 0);
   My_Lists.Append (L, 0);
   My_Lists.Append (L, 0);
   pragma Assert (for all E : Integer of C => E = 0);
   pragma Assert (for all I in Iterate (H) => H.C (I) = 0);
   for E of L when E in Natural loop
      pragma Assert (E = 0);
   end loop;
end Bad_Iterators;
