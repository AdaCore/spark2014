with Ada.Containers.Formal_Hashed_Sets;
with Ada.Containers; use Ada.Containers;
package P is pragma SPARK_Mode (On);

   type Element_Type is new Integer range 1 .. 100;

   function My_Eq (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 = I2);

   function Hash (Id : Element_Type) return Hash_Type is (Hash_Type (Id));

   package My_Sets is new Ada.Containers.Formal_Hashed_Sets
     (Element_Type, Hash, My_Eq);
   use My_Sets; use My_Sets.Formal_Model;

   procedure My_Include (L : in out Set; E : Element_Type) with
     Pre => Contains (L, E) or Length (L) < L.Capacity,
     Post => Element (L, Find (L, E)) = E;

   procedure Identity (L : in out Set; E : Element_Type) with
     Pre => Length (L) < L.Capacity and not Contains (L, E),
     Post => L = L'Old and
     (for all C in L => Has_Element (L'Old, C)
       and Element (L, C) = Element (L'Old, C));

   procedure Nearly_Identity (L : in out Set; Cu : in out Cursor) with
     Pre => Has_Element (L, Cu),
     Post => L = L'Old and
     (if Cu = Cu'Old then
         (for all C in L => Has_Element (L'Old, C)
           and Element (L, C) = Element (L'Old, C)));

end P;
