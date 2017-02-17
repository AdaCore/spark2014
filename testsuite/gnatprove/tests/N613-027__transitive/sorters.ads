package Sorters
   with SPARK_Mode
is
   type Array_Type is array (Positive range <>) of Integer;

   function Perm (A : in Array_Type;
                  B : in Array_Type) return Boolean
   -- Returns True is A is a permuation of B
     with
       Global => null,
       Ghost, Import;


   -- Sorts the elements in the array Values in ascending order
   procedure Selection_Sort (Values : in out Array_Type) with
     Depends => (Values => Values),
     Pre     => Values'Length >= 1 and then
     Values'Last   <= Positive'Last,
     Post    => Perm (Values'Old, Values) and then
     (for all J in Values'First .. Values'Last - 1 =>
        Values (J) <= Values (J + 1));
end Sorters;
