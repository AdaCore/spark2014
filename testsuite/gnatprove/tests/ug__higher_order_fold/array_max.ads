with SPARK.Higher_Order.Fold;

package Array_Max is

   type Int_Array is array (Positive range <>) of Integer;

   function Max_Prefix
     (A : Int_Array; X : Integer; I : Positive) return Boolean
   is (for all K in A'First .. I - 1 => A (K) <= X)
   with Ghost, Pre => I in A'Range;
   --  X is greater than or equal to all the elements of A before I

   function Max_All (A : Int_Array; X : Integer) return Boolean
   is (for all K in A'Range => A (K) <= X)
   with Ghost;
   --  X is greater than or equal to all the elements of A

   function Max (E : Integer; X : Integer) return Integer
   is (Integer'Max (E, X));

   package Fold_Max is new SPARK.Higher_Order.Fold.Fold_Left
     (Index_Type  => Positive,
      Element_In  => Integer,
      Array_Type  => Int_Array,
      Element_Out => Integer,
      Ind_Prop    => Max_Prefix,
      Final_Prop  => Max_All,
      F           => Max);

   function Max_Element (A : Int_Array) return Integer
   is (Fold_Max.Fold (A, Integer'First))
   with Post => Max_All (A, Max_Element'Result);

end Array_Max;
