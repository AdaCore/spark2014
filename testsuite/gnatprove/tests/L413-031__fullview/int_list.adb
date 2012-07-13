pragma Ada_2012;
with Ada.Containers.Formal_Doubly_Linked_Lists;

procedure Int_List is
   function My_Eq (I1 : Integer; I2 : Integer) return Boolean
   is (I1 = I2);

   package MyLists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Integer, "=" => My_Eq);
   use MyLists;

   procedure Add (L : in out List; I : Integer) with
     Post => Element (L, First (L)) = I
       and then (for all C in L'Old => Element (L, C) = Element (L'Old, C));

   procedure Add (L : in out List; I : Integer) is
   begin
      Prepend (L, I);
   end Add;

   L : List (10);
begin
   Add (L, 0);
   Add (L, 1);
end Int_List;
