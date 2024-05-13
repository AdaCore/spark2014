pragma SPARK_Mode (On);

package Sorted_Vectors is
    Capacity : constant Positive := 100;

    type Vector is private;

private

    type Base_Array is array (Positive range <>) of Integer;

    function Sorted (A : Base_Array) return Boolean
    is (A'Length <= 1
        or else
            (for all J in A'First + 1 .. A'Last => A (J - 1) <= A (J)));

    type Base_Vector is record
        Length : Natural range 0 .. Capacity := 0;
        Arr : Base_Array (1 .. Capacity);
    end record;

    function "+" (V : Base_Vector) return Base_Array
    is (V.Arr (1 .. V.Length));

    type Vector is new Base_Vector;
    pragma Type_Invariant (Vector, Sorted (+Vector));

end Sorted_Vectors;
