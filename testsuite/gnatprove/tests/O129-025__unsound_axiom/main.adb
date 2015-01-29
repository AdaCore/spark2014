procedure Main
is
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

   Null_Node : constant Node_Type :=
     (Variant_Node => (M_Variant => Empty_Node));

   procedure Create_Empty_Branch
     (Branch       : out Node_Type)
   with
     Pre     => True,
     Post    => False
   is
   begin
      pragma Assert (False);  --@ASSERT:FAIL
      Branch := Null_Node;
   end Create_Empty_Branch;

   X : Node_Type;
begin

   pragma Warnings (Off, "statement has no effect");
   pragma Warnings (Off, "unused assignment");

   Create_Empty_Branch
     (Branch       => X);

   pragma Assert (True = False);

end Main;
