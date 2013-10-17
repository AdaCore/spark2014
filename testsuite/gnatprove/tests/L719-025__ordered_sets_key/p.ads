with Ada.Containers.Formal_Ordered_Sets;
with Ada.Containers; use Ada.Containers;
package P is pragma SPARK_Mode (On);

   type Element_Type is new Integer range 1 .. 100;

   function My_Eq (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 = I2);

   function My_Inf (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 < I2);

   package My_Sets is new Ada.Containers.Formal_Ordered_Sets
     (Element_Type => Element_Type, "=" => My_Eq, "<" => My_Inf);
   use My_Sets;

   subtype Key_Type is Element_Type;

   function Key (I : Element_Type) return Key_Type is (I);

   package My_Keys is new Generic_Keys
     (Key_Type, Key, "<" => My_Inf);
   use My_Keys;

   procedure Identity (L : in out Set; K : Key_Type) with
     Pre => My_Keys.Contains (L, K),
     Post => Strict_Equal (L, L'Old);

end P;
