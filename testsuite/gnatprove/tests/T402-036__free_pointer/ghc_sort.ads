pragma SPARK_Mode;
package GHC_Sort is
   type Int_Array is array (Positive range <>) of Integer;
   function Sort (S : Int_Array) return Int_Array;
end GHC_Sort;
