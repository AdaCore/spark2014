with SPARK.Higher_Order;
with SPARK.Higher_Order.Fold;
with Test_Types; use Test_Types;
package Test_Higher_Order1 with SPARK_Mode is

   function Ind_Prop
     (A : My_Matrix; X : Integer; I : My_Index; J : My_Index_2) return Boolean
     with Pre => I in A'Range (1) and then J in A'Range (2);
   --  Ind_Prop cannot have another precondition, or Prove_Ind_Col,
   --  Prov_Ind_Row, and Prove_Last would not be self guarded.

   function Final_Prop (A : My_Matrix; X : Integer) return Boolean
     with Pre => A'Length (1) > 0 and then A'Length (2) > 0;
   --  Final_Prop is always called after Prove_Last, which has the same
   --  application of Final_Prop as a post. There can be no error.

   function F_2 (X : Integer; I : Integer) return Integer;
   --  F_2 is always called on A (I, J), X when Ind_Prop (A, X, I, J) is True.
   --  It is called in the same conditions in Prove_Ind_Col, Prov_Ind_Row, and
   --  Prove_Last.

   package My_Fold_2 is new SPARK.Higher_Order.Fold.Fold_2
     (Index_1     => My_Index,
      Index_2     => My_Index_2,
      Element_In  => Integer,
      Array_Type  => My_Matrix,
      Element_Out => Integer,
      Ind_Prop    => Ind_Prop,
      Final_Prop  => Final_Prop,
      F           => F_2);

end Test_Higher_Order1;
