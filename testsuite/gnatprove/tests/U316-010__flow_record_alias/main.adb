procedure Main
is
   type Node_Variant_Type (M_Variant : Integer := 0) is
      record
         C : Integer := 0;
      end record;

   type Node_Type is
      record
         Variant_Node : Node_Variant_Type;
      end record;

   Null_Node : Node_Type := (Variant_Node => (M_Variant => 0, C => 0));
   Alias : Node_Type with Address => Null_Node'Address, Import;

   type Branch_Type is
      record
         N : Node_Type;
      end record;

   procedure Create_Empty_Branch
     (Branch : out Branch_Type)
   with
     Global  => Null_Node,
     Depends => (Branch => Null_Node)
   is
   begin
      Branch.N := Alias;
   end Create_Empty_Branch;

begin
   null;
end Main;
