with Ada.Containers.Formal_Ordered_Maps;
with Ada.Containers; use Ada.Containers;
package P is pragma SPARK_Mode (On);

   type Element_Type is new Integer range 1 .. 100;
   type Key_Type is new Integer range 1 .. 100;

   function My_Eq (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 = I2);

   function My_Inf (I1 : Key_Type; I2 : Key_Type) return Boolean is
     (I1 < I2);

   package My_Maps is new Ada.Containers.Formal_Ordered_Maps
     (Key_Type,Element_Type, "=" => My_Eq, "<" => My_Inf);
   use My_Maps;

   procedure My_Include (L : in out Map; K : Key_Type; E : Element_Type) with
     Pre => Contains (L, K) or Length (L) < L.Capacity,
     Post => Contains (L, K) and Element (L, K) = E;

   procedure Identity (L : in out Map; K : Key_Type) with
     Pre => Length (L) < L.Capacity and not Contains (L, K),
     Post => Strict_Equal (L, L'Old);

   procedure Nearly_Identity (L : in out Map; K : Key_Type) with
     Pre => Contains (L, K),
     Post => L = L'Old and
     (if Find (L, K) = Find (L'Old, K) then Strict_Equal (L, L'Old));

end P;
