with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with SPARK.Higher_Order;
with SPARK.Higher_Order.Fold;
with Test_Types; use Test_Types;
package Test_Higher_Order3 with SPARK_Mode is

   function Value (X : Integer) return My_Small
     with Global   => null,
          Import,
          Annotate => (GNATprove, Always_Return);
   --  Value cannot have a pre as it is called from Add_Value without any
   --  constraint.

   function Choose (X : Integer) return Boolean
     with Global   => null,
          Import,
          Annotate => (GNATprove, Always_Return);
   --  Value cannot have a pre as it is called from Add_One without any
   --  constraint.

   package My_Count is new SPARK.Higher_Order.Fold.Count
     (Index_Type  => Small_Index,
      Element     => Integer,
      Array_Type  => Small_Array,
      Choose      => Choose);

   function Valid_Integer (Arg : Big_Integer) return Boolean is
     (In_Range (Arg,
      Low  => To_Big_Integer (Integer'First),
      High => To_Big_Integer (Integer'Last)));

   package My_Sum_Int is new SPARK.Higher_Order.Fold.Sum_2
     (Index_1     => Small_Index,
      Index_2     => Small_Index,
      Element_In  => Integer,
      Element_Out => Integer,
      Zero        => 0,
      Add         => "+",
      To_Big      => To_Big_Integer,
      In_Range    => Valid_Integer,
      Array_Type  => Small_Matrix,
      Value       => Value);

   procedure Prove_No_Overflows (A : Small_Matrix) with
     Ghost,
     Global => null,
     Post => My_Sum_Int.No_Overflows (A);

   function Sum_Int (A : Small_Matrix) return Integer with
     Post => To_Big_Integer (Sum_Int'Result) =
       My_Sum_Int.Big_Integer_Sum.Sum (A);

   function In_Range (X : Big_Integer) return Boolean
     with Global   => null,
          Import,
          Ghost,
          Annotate => (GNATprove, Always_Return);

   function To_Big (X : Integer) return Big_Integer
     with Global   => null,
          Import,
          Ghost,
          Annotate => (GNATprove, Always_Return);

   function Add_Pre (X, Y : Integer) return Boolean
     with Global   => null,
          Import,
          Annotate => (GNATprove, Always_Return);

   function Add (X, Y : Integer) return Integer
     with Global   => null,
          Import,
          Pre      => Add_Pre (X, Y),
          Annotate => (GNATprove, Always_Return);

   package My_Sum_2 is new SPARK.Higher_Order.Fold.Sum_2
     (Index_1     => Small_Index,
      Index_2     => Small_Index,
      Element_In  => Integer,
      Element_Out => Integer,
      Zero        => 0,
      Add         => Add,
      To_Big      => To_Big,
      In_Range    => In_Range,
      Array_Type  => Small_Matrix,
      Value       => Value);

   package My_Count_2 is new SPARK.Higher_Order.Fold.Count_2
     (Index_1     => Small_Index,
      Index_2     => Small_Index,
      Element     => Integer,
      Array_Type  => Small_Matrix,
      Choose      => Choose);

end Test_Higher_Order3;
