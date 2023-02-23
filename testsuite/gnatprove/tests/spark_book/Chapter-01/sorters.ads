pragma Spark_Mode (On);
package Sorters is

   type Array_Type is array (Positive range <>) of Integer;

   function Perm (A : in Array_Type;
                  B : in Array_Type) return Boolean
   -- Returns True if A is a permuation of B
     with Global => null,
          Ghost  => True,
          Import => True;

   procedure Selection_Sort (Values : in out Array_Type)
   -- Sorts the elements in the array Values in ascending order
     with Depends => (Values => Values),
          Pre     => Values'Length >= 1 and then
                     Values'Last   <= Positive'Last,
          Post    => (for all J in Values'First .. Values'Last - 1 =>
                        Values (J) <= Values (J + 1))  and then
                      Perm (Values'Old, Values);
end Sorters;
