with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Higher_Order.Fold;
package Sum_Test with
    SPARK_Mode => On,
    Annotate => (GNATprove, Always_Return)
is

   Big_Int_First : constant Big_Integer := To_Big_Integer(Integer'First);
   Big_Int_Last  : constant Big_Integer := To_Big_Integer(Integer'Last);
   subtype Big_Int_Type is Big_Integer with
     Dynamic_Predicate => (
                             Big_Int_Type >= Big_Int_First and then
                               Big_Int_Type <= Big_Int_Last);
    type Int_Array_Type is array (Positive range <>) of Integer;

   function To_Big_Int_Type (X : Integer) return Big_Int_Type is
     (To_Big_Integer(X));

    function Prefix_Sums_To_Big (X : Big_Integer) return Big_Integer is (X);
    function Prefix_Sums_In_Range (X : Big_Integer) return Boolean is (X = X);
    package Prefix_Sums_Parent is new SPARK.Higher_Order.Fold.Sum(
        Index_Type => Positive,
        Element_In => Integer,
        Array_Type => Int_Array_Type,
        Element_Out => Big_Integer,
        Add => "+",
        Zero => 0,
        To_Big => Prefix_Sums_To_Big,
        In_Range => Prefix_Sums_In_Range,
        Value => To_Big_Int_Type);

end Sum_Test;
