pragma Ada_2012;
with Ada.Containers.Formal_Doubly_Linked_Lists; use Ada.Containers;

package Int_List is pragma SPARK_Mode (On);

   subtype My_Int is Integer range 1 .. 100;

   function My_Eq (I1 : My_Int; I2 : My_Int) return Boolean is (I1 = I2);

   package My_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (My_Int);
   use My_Lists; use Formal_Model;

   procedure Add (L : in out List; I : My_Int) with
     Pre  => Length (L) < L.Capacity,
     Post =>
       Element (L, First (L)) = I
         and then
         Length (L) = Length (L'Old) + 1
     and then
       (for all C in L'Old => Element (L, C) = Element (L'Old, C));

   procedure Incr (L : in out List) with
     Pre  => (for all C in L => Element (L, C) < My_Int'Last),
     Post =>
       Length (L) = Length (L'Old) and then
     (for all C in L => Has_Element (L'Old, C) and then
          Element (L, C) = Element (L'Old, C) + 1);
end Int_List;
