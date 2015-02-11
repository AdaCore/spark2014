with Tree_Logic;

package Primitives
with SPARK_Mode
is

   package TL renames Tree_Logic;

   type Primitive_Type
      (M_IO_Error  : Boolean := False)
     is record
        M_Read_Branch   : TL.Branch_Type (TL.VBD_Tree);
        M_Read_Iterator : TL.Branch_Read_Iterator_Type;
     end record;

   procedure Update_Context (Primitive : in out Primitive_Type);

end Primitives;
