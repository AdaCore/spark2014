with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers; use Ada.Containers;
package My_Lists is
   pragma SPARK_Mode (On);

   type Element_Type is new Integer range 0 .. 100;

   function My_Eq (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 = I2);

   package My_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type);

   use My_Lists;

   subtype C_List1 is List (100);

   type C_List2 is new List (100);

   subtype List1 is List;

   type List2 is new List;

   subtype C_List11 is List1 (100);

   type C_List12 is new List1 (100);

   subtype C_List21 is List2 (100);

   type C_List22 is new List2 (100);

   procedure P;
end;
