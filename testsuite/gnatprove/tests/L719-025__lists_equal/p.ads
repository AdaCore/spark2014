with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers; use Ada.Containers;
package P is pragma SPARK_Mode (On);

   type Element_Type is new Integer range 1 .. 100;

   function My_Eq (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 = I2);

   package My_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type, My_Eq);
   use My_Lists;

   procedure Identity (L : in out List; Cu : in out Cursor) with
     Pre => Length (L) < L.Capacity and
     (Has_Element (L, Cu) or Cu = No_Element),
     Post => Strict_Equal (L, L'Old) and Cu = No_Element;

   procedure Nearly_Identity (L : in out List; Cu : in out Cursor) with
     Pre => Has_Element (L, Cu),
     Post =>
     (if Cu = Cu'Old then Strict_Equal (L, L'Old));

   procedure Identity_Swap (L : in out List; Cu1 : Cursor; Cu2 : Cursor) with
     Pre => Has_Element (L, Cu1) and Has_Element (L, Cu2),
     Post => Strict_Equal (L, L'Old);

   procedure Identity_Swap_Links (L : in out List; Cu1 : Cursor; Cu2 : Cursor)
   with
     Pre => Has_Element (L, Cu1) and Has_Element (L, Cu2),
     Post => Strict_Equal (L, L'Old);

end P;
