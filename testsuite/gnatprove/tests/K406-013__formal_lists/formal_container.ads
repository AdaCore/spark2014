with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers;
use Ada.Containers;

package Formal_Container is
   function My_Eq (I1, I2 : Integer) return Boolean is (I1 = I2);
   package VDLL is new Formal_Doubly_Linked_Lists
     (Element_Type => Integer);
end Formal_Container;
