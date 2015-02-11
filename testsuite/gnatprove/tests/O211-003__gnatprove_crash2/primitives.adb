package body Primitives
with SPARK_Mode
is

   procedure Update_Context (Primitive : in out Primitive_Type)
   is
   begin

      TL.Insert
        (Primitive.M_Read_Branch,
         Primitive.M_Read_Iterator);

   end Update_Context;


end Primitives;
