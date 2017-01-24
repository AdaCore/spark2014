with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers; use Ada.Containers;
package P is pragma SPARK_Mode (On);

   type Element_Type is new Integer range 1 .. 100;

   package My_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type);
   use My_Lists; use Formal_Model;

   procedure Identity (L : in out List; Cu : in out Cursor) with
     Pre => Length (L) < L.Capacity and
     (Has_Element (L, Cu) or Cu = No_Element),
     Post => Model (L) = Model (L)'Old
     and Positions (L) = Positions (L)'Old
     and Cu = No_Element;

   procedure Nearly_Identity (L : in out List; Cu : in out Cursor) with
     Pre => Has_Element (L, Cu),
     Post => Model (L) = Model (L)'Old
     and (if Cu = Cu'Old then Positions (L) = Positions (L'Old));

   procedure Identity_Swap (L : in out List; Cu1 : Cursor; Cu2 : Cursor) with
     Pre => Has_Element (L, Cu1) and Has_Element (L, Cu2),
     Post => Model (L) = Model (L)'Old
     and Positions (L) = Positions (L)'Old;

   procedure Identity_Swap_Links (L : in out List; Cu1 : Cursor; Cu2 : Cursor)
   with
     Pre => Has_Element (L, Cu1) and Has_Element (L, Cu2),
     Post => Model (L) = Model (L)'Old
     and Positions (L) = Positions (L)'Old;

end P;
