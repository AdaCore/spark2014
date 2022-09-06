with SPARK.Higher_Order;
with SPARK.Higher_Order.Fold;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
package Test_Higher_Order with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   function Small_Enough (X : Natural) return Boolean is
     (X < Integer'Last);

   function Add_One (X : Integer) return Integer is (X + 1) with
     Pre => X < Integer'Last;

   function Add_All is new SPARK.Higher_Order.Map
     (Index_Type  => Positive,
      Element_In  => Natural,
      Array_In    => Nat_Array,
      Element_Out => Natural,
      Array_Out   => Nat_Array,
      Init_Prop   => Small_Enough,
      F           => Add_One);

   function A_Small_Enough (X : Integer) return Boolean is
     (X < Integer'Last);

   procedure Add_All is new SPARK.Higher_Order.Map_Proc
     (Index_Type => Positive,
      Element    => Natural,
      Array_Type => Nat_Array,
      Init_Prop  => A_Small_Enough,
      F          => Add_One);

   subtype Small_Int is Integer range - 100 .. 100;

   subtype Small_Index is Positive range 1 .. 100;

   type Small_Int_Array is array (Small_Index range <>) of Small_Int;

   function In_Range (A : Small_Int_Array; X : Integer; I : Small_Index)
                      return Boolean
   is (X in Integer'First + 100 * (I - A'First + 1) .. Integer'Last - 100 * (I - A'First + 1))
     with Pre => I in A'Range;

   function Result_In_Range (A : Small_Int_Array; X : Integer) return Boolean is (True);

   package Sum is new SPARK.Higher_Order.Fold.Fold_Right
     (Index_Type  => Small_Index,
      Element_In  => Small_Int,
      Array_Type  => Small_Int_Array,
      Element_Out => Integer,
      Ind_Prop    => In_Range,
      Final_Prop  => Result_In_Range,
      F           => "+");

   type Matrix is array (Small_Index range <>, Small_Index range <>) of Small_Int;

   function In_Range (A : Matrix; X : Integer; I, J : Small_Index)
                      return Boolean
   is (X <= Integer'Last - 100 * ((A'Last (1) - I) * A'Length (2) + A'Last (2) - J + 1)
       and X >= Integer'First + 100 * ((A'Last (1) - I) * A'Length (2) + A'Last (2) - J + 1))
     with Pre => I in A'Range (1) and then J in A'Range (2),
     Post => (if In_Range'Result then X <= Integer'Last - 100 and then X >= Integer'First + 100);

   function Result_In_Range (A : Matrix; X : Integer) return Boolean is (True);

   package Sum_2 is new SPARK.Higher_Order.Fold.Fold_2
     (Index_1     => Small_Index,
      Index_2     => Small_Index,
      Element_In  => Small_Int,
      Array_Type  => Matrix,
      Element_Out => Integer,
      Ind_Prop    => In_Range,
      Final_Prop  => Result_In_Range,
      F           => "+");

   function Id (X : Small_Int) return Small_Int is (X);

   function In_Range (X : Big_Integer) return Boolean is
     (In_Range
        (X, To_Big_Integer (Integer'First), To_Big_Integer (Integer'Last)));

   package Sum_l is new SPARK.Higher_Order.Fold.Sum
     (Index_Type  => Small_Index,
      Element_In  => Small_Int,
      Element_Out => Integer,
      Add         => "+",
      Zero        => 0,
      To_Big      => To_Big_Integer,
      In_Range    => In_Range,
      Array_Type  => Small_Int_Array,
      Value       => Id);

   pragma Assert (Sum_l.Sum (A => (1, 2, 3, 4, 5, 6, 7, 1, 1)) = 30);

   function Is_Pos (X : Small_Int) return Boolean is (X >= 0);

   package Cnt is new SPARK.Higher_Order.Fold.Count
     (Index_Type  => Small_Index,
      Element     => Small_Int,
      Array_Type  => Small_Int_Array,
      Choose      => Is_Pos);

   pragma Assert (Cnt.Count (A => (1, -2, 3, -4, -5, 6, 7, 13, 0)) = 6);

   package Sum2_l is new SPARK.Higher_Order.Fold.Sum_2
     (Index_1     => Small_Index,
      Index_2     => Small_Index,
      Element_In  => Small_Int,
      Element_Out => Integer,
      Add         => "+",
      Zero        => 0,
      To_Big      => To_Big_Integer,
      In_Range    => In_Range,
      Array_Type  => Matrix,
      Value       => Id);

   pragma Assert (Sum2_l.Sum (A => (1 => (1, 2, 3, 4, 5, 6, 7),
                                    2 => (1, 2, 3, 4, 5, 6, 7))) = 56);

   package Cnt2 is new SPARK.Higher_Order.Fold.Count_2
     (Index_1     => Small_Index,
      Index_2     => Small_Index,
      Element     => Small_Int,
      Array_Type  => Matrix,
      Choose      => Is_Pos);

   pragma Assert (Cnt2.Count (A => (1 => (1, -2, 3, -4, -5, 6, 7, 13, 0),
                                    2 => (1, -2, 3, -4, -5, 6, 7, 13, 0),
                                    3 => (1, -2, 3, -4, -5, 6, 7, 13, -1))) = 17);

end Test_Higher_Order;
