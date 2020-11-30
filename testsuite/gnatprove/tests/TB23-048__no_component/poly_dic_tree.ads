with Ada.Unchecked_Deallocation;

package Poly_Dic_Tree with SPARK_Mode is
   type Tagged_Data_Type is abstract tagged null record;
   type Tagged_Data_Access_Type is access all Tagged_Data_Type'Class;

   type Dictionary_Tree_Type is limited private;
private

   type Node_Access_Type is access Dictionary_Tree_Type;

   type Dictionary_Tree_Type is record
      Tagged_Data_Access : Tagged_Data_Access_Type := null;
   end record;

   procedure Free_Node is new Ada.Unchecked_Deallocation
     (Object => Dictionary_Tree_Type, Name => Node_Access_Type);

end Poly_Dic_Tree;
