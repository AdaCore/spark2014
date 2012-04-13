pragma Ada_2012;
with Ada.Containers.Formal_Doubly_Linked_Lists;

procedure Int_List is
   function my_eq (I1 : Integer; I2 : Integer) return Boolean
   is (I1 = I2);

   package MyLists is new Ada.Containers.Formal_Doubly_Linked_Lists
        (Integer, "=" => my_eq);
   use MyLists;

   procedure Add (L : in out List; I : Integer) with
   Post => Element (L, First (L)) = I;

   procedure Add (L : in out List; I : Integer) is
   begin
            Prepend (L, I);
   end Add;

begin
   null;
end Int_List;
