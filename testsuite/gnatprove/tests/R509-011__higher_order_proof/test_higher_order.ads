-------------------------------------------------------------------------------
--                                    README                                 --
--                                                                           --
--  This test aims at proving the correctness of Fold when bodies are hidden --
--  Everything should be proved but the axioms in the three Fold theories    --
--  (7 unproved checks in SPARK.Higher_Order.Fold.ads)                       --
-------------------------------------------------------------------------------

with SPARK.Higher_Order;
with SPARK.Higher_Order.Fold;
package Test_Higher_Order with SPARK_Mode is

   package Nested is
      function Id (X : Integer) return Integer;
      pragma Annotate (GNATprove, Terminating, Id);
   private
      pragma SPARK_Mode (Off);
      function Id (X : Integer) return Integer is (X);
   end Nested;
   use Nested;

   Fst : constant Integer := Id (0);
   Lst : constant Integer := Id (100);

   subtype My_Index is Integer range Fst .. Lst;

   type My_Array is array (My_Index range <>) of Integer;

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

   Fst2 : constant Integer := Id (1);
   Lst2 : constant Integer := Id (200);

   subtype My_Index_2 is Integer range Fst2 .. Lst2;

   type My_Matrix is array (My_Index range <>, My_Index_2 range <>) of Integer;

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

   subtype Small_Index is Integer range 1 .. 100;

   subtype My_Small is Integer range -100 .. 100;

   type Small_Array is array (Small_Index range <>) of Integer;
   --  There cannot be any overflow in the computation if Result_In_Range does
   --  not overflow.

   function Value (X : Integer) return My_Small;
   --  Value cannot have a pre as it is called from Add_Value without any
   --  constraint.

   package My_Sum is new SPARK.Higher_Order.Fold.Sum
     (Index_Type  => Small_Index,
      Element_In  => Integer,
      Array_Type  => Small_Array,
      Element_Out => My_Small,
      Value       => Value);

   function Choose (X : Integer) return Boolean;
   --  Value cannot have a pre as it is called from Add_One without any
   --  constraint.

   package My_Count is new SPARK.Higher_Order.Fold.Count
     (Index_Type  => Small_Index,
      Element     => Integer,
      Array_Type  => Small_Array,
      Choose      => Choose);

   type Small_Matrix is array (Small_Index range <>, Small_Index range <>) of Integer;

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

end Test_Higher_Order;
