with Ada.Containers.Formal_Ordered_Sets;
with Ada.Containers; use Ada.Containers;
package P is pragma SPARK_Mode (On);
   pragma Unevaluated_Use_Of_Old (Allow);

   type Element_Type is new Integer range 1 .. 100;

   function My_Lt (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 < I2) with Annotate => (GNATprove, Inline_For_Proof);

   package My_Sets is new Ada.Containers.Formal_Ordered_Sets
     (Element_Type, "<" => My_Lt);
   use My_Sets; use My_Sets.Formal_Model;

   procedure My_Include (L : in out Set; E : Element_Type) with
     Pre => Contains (L, E) or Length (L) < L.Capacity,
     Post => Element (L, Find (L, E)) = E;

   procedure Identity (L : in out Set; E : Element_Type) with
     Pre => Length (L) < L.Capacity and not Contains (L, E),
     Post => L = L'Old  and then Elements (L) = Elements (L)'Old and then
     Positions (L) = Positions (L'Old);

   procedure Nearly_Identity (L : in out Set; Cu : in out Cursor) with
     Pre => Has_Element (L, Cu),
     Post => L = L'Old and then Elements (L) = Elements (L)'Old and then
     (if Cu = Cu'Old then Positions (L) = Positions (L)'Old);

end P;
