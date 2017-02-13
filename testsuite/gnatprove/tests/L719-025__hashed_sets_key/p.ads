with Ada.Containers.Formal_Hashed_Sets;
with Ada.Containers; use Ada.Containers;
package P is pragma SPARK_Mode (On);

   type Element_Type is new Integer range 1 .. 100;

   function My_Eq (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 = I2);

   function Hash (Id : Element_Type) return Hash_Type is (Hash_Type (Id));

   package My_Sets is new Ada.Containers.Formal_Hashed_Sets
     (Element_Type, Hash, My_Eq);
   use My_Sets;

   subtype Key_Type is Element_Type;

   function Key (I : Element_Type) return Key_Type is (I);

   package My_Keys is new Generic_Keys
     (Key_Type, Key, Hash, My_Eq);
   use My_Keys;

   procedure Identity (L : in out Set; K : Key_Type) with
     Pre => My_Keys.Contains (L, K),
     Post => L = L'Old;

end P;
