package Binary_Search_Trees is

   type Tree_Node;
   type Node_Access is access Tree_Node;

   type Tree_Node is
      record
         Data  : Integer;
         Left  : Node_Access;
         Right : Node_Access;
      end record;

   Dummy : Boolean := True;
   --  This dummy global is needed, as otherwise the part of flow analysis
   --  that we intend to test here will be skiped.

   procedure Invalidate (Starting_At : not null Node_Access)
   with Global => (In_Out => Dummy);

end Binary_Search_Trees;
