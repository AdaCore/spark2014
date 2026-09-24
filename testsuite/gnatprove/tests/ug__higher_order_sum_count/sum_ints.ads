with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Higher_Order.Fold;

package Sum_Ints is

   type Int_Array is array (Positive range <>) of Integer;

   function In_Integer_Range (X : Big_Integer) return Boolean
   is (In_Range (X, To_Big_Integer (Integer'First),
                    To_Big_Integer (Integer'Last)))
   with Ghost;

   function Add (Left, Right : Integer) return Integer is (Left + Right)
   with
     Pre => In_Integer_Range (To_Big_Integer (Left) + To_Big_Integer (Right));

   function Value (X : Integer) return Integer is (X);

   package Sum_All is new SPARK.Higher_Order.Fold.Sum
     (Index_Type  => Positive,
      Element_In  => Integer,
      Array_Type  => Int_Array,
      Element_Out => Integer,
      Add         => Add,
      Zero        => 0,
      To_Big      => To_Big_Integer,
      In_Range    => In_Integer_Range,
      Value       => Value);

end Sum_Ints;
