with SPARK.Higher_Order;
with SPARK.Higher_Order.Fold;
with Test_Types; use Test_Types;
package Test_Higher_Order3 with SPARK_Mode is

   function Value (X : Integer) return My_Small;
   --  Value cannot have a pre as it is called from Add_Value without any
   --  constraint.

   function Choose (X : Integer) return Boolean;
   --  Value cannot have a pre as it is called from Add_One without any
   --  constraint.

   package My_Count is new SPARK.Higher_Order.Fold.Count
     (Index_Type  => Small_Index,
      Element     => Integer,
      Array_Type  => Small_Array,
      Choose      => Choose);

   package My_Sum_2 is new SPARK.Higher_Order.Fold.Sum_2
     (Index_1     => Small_Index,
      Index_2     => Small_Index,
      Element_In  => Integer,
      Array_Type  => Small_Matrix,
      Element_Out => My_Small,
      Value       => Value);

   package My_Count_2 is new SPARK.Higher_Order.Fold.Count_2
     (Index_1     => Small_Index,
      Index_2     => Small_Index,
      Element     => Integer,
      Array_Type  => Small_Matrix,
      Choose      => Choose);


end Test_Higher_Order3;
