procedure Main
is
   Maximum_Tree_Height : constant := 2 ** 4 - 1;
   type Tree_Height_Type is range 0 .. Maximum_Tree_Height;
   subtype Subtree_Height_Type is Tree_Height_Type range 0 .. Tree_Height_Type'Last - 1;
   type Node_Enum is (Empty_Node);

   type Node_Variant_Type (M_Variant : Node_Enum := Empty_Node) is
      record
         case M_Variant is
            when Empty_Node =>
               null;
         end case;
      end record;

   type Node_Type is
      record
         Variant_Node : Node_Variant_Type;
      end record;

   Null_Node : constant Node_Type := (Variant_Node => (M_Variant => Empty_Node));

   type Branch_Type (M_Height : Subtree_Height_Type) is
      record
         N : Node_Type;
      end record;

   procedure Create_Empty_Branch
     (Branch       : out Branch_Type)
   with
     Global  => null,
     depends => (Branch =>+ null)
   is
   begin
      Branch.N := Null_Node;

   end Create_Empty_Branch;

   X : Branch_Type (7);
begin


   pragma Warnings (Off, "statement has no effect");
   pragma Warnings (Off, "unused assignment");
   Create_Empty_Branch
     (Branch       => X);

end Main;
