pragma Ada_2012;
with Ada.Containers.Formal_Doubly_Linked_Lists; use Ada.Containers;

package Int_List is pragma SPARK_Mode (On);
  type my_record (capacity : Integer) is private;

   subtype My_Int is Integer range 1 .. 100;

   function My_Eq (I1 : My_Int; I2 : My_Int) return Boolean is (I1 = I2);

   package My_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (My_Int, "=" => My_Eq);
   use My_Lists;

   procedure Add (L : in out List; I : My_Int) with
     Pre  => Length (L) < L.Capacity,
     Post =>
       Element (L, First (L)) = I
         and then
       Length (L) = Length (L'Old) + 1;
--         and then
--       (for all C in L'Old.Iterate => Element (L, C) = Element (L'Old, C));

   procedure Incr (L : in out List) with
--     Pre  => (for all C in L.Iterate => Element (L, C) < My_Int'Last),
     Post =>
       Length (L) = Length (L'Old);
--         and then
--       (for all C in L.Iterate => Element (L, C) = Element (L'Old, C) + 1);

private
  type my_record (capacity : Integer) is record
    capacity2 : Integer;
  end record;
end Int_List;
