with SPARK.Higher_Order.Fold;

package Count_Zeros is

   type Int_Array is array (Positive range <>) of Integer;

   function Is_Zero (X : Integer) return Boolean is (X = 0);

   package Zeros is new SPARK.Higher_Order.Fold.Count
     (Index_Type => Positive,
      Element    => Integer,
      Array_Type => Int_Array,
      Choose     => Is_Zero);
   use Zeros;

   procedure Reset (A : in out Int_Array; I : Positive)
   with
     Pre  => I in A'Range,
     Post =>
       Count (A) = (if A'Old (I) = 0 then Count (A'Old)
                    else Count (A'Old) + 1);
   --  Set A (I) to zero

end Count_Zeros;
