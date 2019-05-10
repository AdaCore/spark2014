pragma SPARK_Mode;
package Repro is
   type Node_Types is (Element_Node, Attribute_Node);
   type Node_Record (Node_Type : Node_Types) is private;
   type Node is access Node_Record;
   subtype Element is Node (Element_Node);
private
   type Node_Record (Node_Type : Node_Types) is record
      Parent : Node;
   end record;
end Repro;
