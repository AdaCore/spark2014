with Ada.Containers.Formal_Doubly_Linked_Lists; use Ada.Containers;

package Element_Lists with
  SPARK_Mode
is
   type Element_Type is new Integer;

   package Lists is new Formal_Doubly_Linked_Lists (Element_Type);

end Element_Lists;
