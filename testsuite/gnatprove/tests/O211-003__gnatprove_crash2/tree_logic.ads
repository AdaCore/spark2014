package Tree_Logic is

   type Subtree_Enum is (VBD_Tree, FL_Tree);

   type Branch_Type (M_Variant : Subtree_Enum := VBD_Tree) is
     record
       M_Logical_Address : Integer;
     end record;

   type Branch_Read_Iterator_Type is
     record
       M_Is_Valid : Boolean;
     end record;


   procedure Insert
     (Branch   : in out Branch_Type;
      Iterator : in out Branch_Read_Iterator_Type);


end Tree_Logic;
