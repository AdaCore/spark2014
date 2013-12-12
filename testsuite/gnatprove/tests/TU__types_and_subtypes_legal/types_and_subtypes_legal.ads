package Types_And_Subtypes_Legal
  with SPARK_Mode
is
   --  TU: 1. The view of an entity introduced by a
   --  ``private_type_declaration`` is in |SPARK| if the types of any
   --  visible discriminants are in |SPARK|, even if the entity
   --  declared by the corresponding ``full_type_declaration`` is not
   --  in |SPARK|.
   type Node is private;

   function Get_Data (N : Node) return Integer;

   function "=" (X, Y : Node) return Boolean is (Get_Data (X) = Get_Data (Y));

   function Get_Next (N : Node) return Node;
private
   pragma SPARK_Mode (Off);

   type Node is record
      Data : Integer := 0;
      Next : access Node := null;
   end record;

   Null_Node : constant Node := Node'(Data => 0, Next => null);
end Types_And_Subtypes_Legal;
