package Sorters
   with SPARK_Mode
is
   type Array_Type is array (Positive range <>) of Integer;

   -- Sorts the elements in the array Values in ascending order
   procedure Selection_Sort (Values : in out Array_Type)
     with
       Depends => (Values => Values),
       Pre     => (Values'Length >= 1),
       Post    => (for all J in Values'First .. Values'Last - 1 =>
                   Values (J) <= Values (J + 1));
end Sorters;
