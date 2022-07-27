with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with SPARK.Higher_Order;
with SPARK.Higher_Order.Fold;
with Test_Types; use Test_Types;
package Test_Higher_Order2 with SPARK_Mode is

   function Ind_Prop (A : My_Array; X : Integer; I : My_Index) return Boolean
     with Import,
          Pre      => I in A'Range,
          Global   => null,
          Annotate => (GNATprove, Always_Return);
   --  Ind_Prop cannot have another precondition, or Prove_Ind and Prove_Last
   --  would not be self guarded.

   function Final_Prop (A : My_Array; X : Integer) return Boolean
     with Import,
          Pre      => A'Length > 0,
          Global   => null,
          Annotate => (GNATprove, Always_Return);
   --  Final_Prop is always called after Prove_Last, which has the same
   --  application of Final_Prop as a post. There can be no error.

   function F (X : Integer; I : Integer) return Integer
     with Import,
          Global   => null,
          Annotate => (GNATprove, Always_Return);
   --  F is always called on A (I), X when Ind_Prop (A, X, I) is True.
   --  It is called in the same conditions in Prove_Ind and Prove_Last.

   function Value (X : Integer) return My_Small
     with Import,
          Global   => null,
          Annotate => (GNATprove, Always_Return);
   --  Value cannot have a pre as it is called from Add_Value without any
   --  constraint.

   function Valid_Integer (Arg : Big_Integer) return Boolean is
     (In_Range (Arg,
      Low  => To_Big_Integer (Integer'First),
      High => To_Big_Integer (Integer'Last)));

   package My_Sum_Int is new SPARK.Higher_Order.Fold.Sum
     (Index_Type  => Small_Index,
      Element_In  => Integer,
      Array_Type  => Small_Array,
      Element_Out => Integer,
      Zero        => 0,
      Add         => "+",
      To_Big      => To_Big_Integer,
      In_Range    => Valid_Integer,
      Value       => Value);

   procedure Prove_No_Overflows (A : Small_Array) with
     Ghost,
     Global => null,
     Post => My_Sum_Int.No_Overflows (A);

   function Sum_Int (A : Small_Array) return Integer with
     Post => To_Big_Integer (Sum_Int'Result) =
       My_Sum_Int.Big_Integer_Sum.Sum (A);

   function In_Range (X : Big_Integer) return Boolean
     with Import,
          Global   => null,
          Ghost,
          Annotate => (GNATprove, Always_Return);

   function To_Big (X : Integer) return Big_Integer
     with Import,
          Global   => null,
          Ghost,
          Annotate => (GNATprove, Always_Return);

   function Add_Pre (X, Y : Integer) return Boolean
     with Import,
          Global   => null,
          Annotate => (GNATprove, Always_Return);

   function Add (X, Y : Integer) return Integer
     with Import,
          Global   => null,
          Pre      => Add_Pre (X, Y),
          Annotate => (GNATprove, Always_Return);

   package My_Sum is new SPARK.Higher_Order.Fold.Sum
     (Index_Type  => Small_Index,
      Element_In  => Integer,
      Array_Type  => Small_Array,
      Element_Out => Integer,
      Zero        => 0,
      Add         => Add,
      To_Big      => To_Big,
      In_Range    => In_Range,
      Value       => Value);

   function F (X : Integer; K : My_Index; I : Integer) return Integer
     with Import,
          Global   => null,
          Annotate => (GNATprove, Always_Return);
   --  F is always called on A (I), I, X when Ind_Prop (A, X, I) is True.
   --  It is called in the same conditions in Prove_Ind and Prove_Last.

   package My_Fold_Left_I is new SPARK.Higher_Order.Fold.Fold_Left_I
     (Index_Type  => My_Index,
      Element_In  => Integer,
      Array_Type  => My_Array,
      Element_Out => Integer,
      Ind_Prop    => Ind_Prop,
      Final_Prop  => Final_Prop,
      F           => F);

end Test_Higher_Order2;
