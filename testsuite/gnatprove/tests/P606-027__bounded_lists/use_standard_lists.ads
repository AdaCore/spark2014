with Ada.Containers.Bounded_Doubly_Linked_Lists;
package Use_Standard_Lists is
   package My_Lists is new Ada.Containers.Bounded_Doubly_Linked_Lists
     (Element_Type => Natural);
end Use_Standard_Lists;
