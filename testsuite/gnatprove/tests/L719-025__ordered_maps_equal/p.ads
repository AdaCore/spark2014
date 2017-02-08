with Ada.Containers.Formal_Ordered_Maps;
with Ada.Containers; use Ada.Containers;
package P is pragma SPARK_Mode (On);

   type Element_Type is new Integer range 1 .. 100;
   type Key_Type is new Integer range 1 .. 100;

   package My_Maps is new Ada.Containers.Formal_Ordered_Maps
     (Key_Type, Element_Type);
   use My_Maps; use Formal_Model;

   procedure My_Include (L : in out Map; K : Key_Type; E : Element_Type) with
     Pre => Contains (L, K) or Length (L) < L.Capacity,
     Post => Contains (L, K) and Element (L, K) = E;

   procedure Identity (L : in out Map; K : Key_Type) with
     Pre => Length (L) < L.Capacity and not Contains (L, K),
     Post => Model (L) = Model (L)'Old and Keys (L) = Keys (L)'Old
     and Positions (L) = Positions (L)'Old;

   procedure Nearly_Identity (L : in out Map; K : Key_Type) with
     Pre => Contains (L, K),
     Post => Model (L) = Model (L)'Old and Keys (L) = Keys (L)'Old and
     (if Find (L, K) = Find (L'Old, K) then Positions (L) = Positions (L'Old));

end P;
