-------------------------------------------------------------------------------
--                                    README                                 --
--                                                                           --
--  This test aims at proving the correctness of Fold when bodies are hidden --
--  Everything should be proved but the axioms in the three Fold theories    --
--  (7 unproved checks in SPARK.Higher_Order.Fold.ads)                       --
-------------------------------------------------------------------------------

with SPARK.Higher_Order;
with SPARK.Higher_Order.Fold;
with Test_Types; use Test_Types;
package Test_Higher_Order with SPARK_Mode is

   function Ind_Prop (A : My_Array; X : Integer; I : My_Index) return Boolean
     with Pre => I in A'Range;
   --  Ind_Prop cannot have another precondition, or Prove_Ind and Prove_Last
   --  would not be self guarded.

   function Final_Prop (A : My_Array; X : Integer) return Boolean
     with Pre => A'Length > 0;
   --  Final_Prop is always called after Prove_Last, which has the same
   --  application of Final_Prop as a post. There can be no error.

   function F (X : Integer; I : Integer) return Integer;
   --  F is always called on A (I), X when Ind_Prop (A, X, I) is True.
   --  It is called in the same conditions in Prove_Ind and Prove_Last.

   package My_Fold_Right is new SPARK.Higher_Order.Fold.Fold_Right
     (Index_Type  => My_Index,
      Element_In  => Integer,
      Array_Type  => My_Array,
      Element_Out => Integer,
      Ind_Prop    => Ind_Prop,
      Final_Prop  => Final_Prop,
      F           => F);

   package My_Fold_Left is new SPARK.Higher_Order.Fold.Fold_Left
     (Index_Type  => My_Index,
      Element_In  => Integer,
      Array_Type  => My_Array,
      Element_Out => Integer,
      Ind_Prop    => Ind_Prop,
      Final_Prop  => Final_Prop,
      F           => F);

end Test_Higher_Order;
