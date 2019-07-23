pragma SPARK_Mode;
package Linked_List_Types_Types is

   type List_Node;
   type List is access List_Node;
   type List_Node is record
      Key  : Character;
      Next : List;
   end record;

end Linked_List_Types_Types;
