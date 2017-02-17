package body Sorters
   with SPARK_Mode
is

   procedure Swap (X      : in Positive;
                   Y      : in Positive;
                   Values : in out Array_Type)
     with
       Depends => (Values => (Values, X, Y)),
       Pre =>
         X /= Y            and then
         X in Values'Range and then
         Y in Values'Range,
         Post =>
           Values (X) = Values'Old (Y) and then
           Values (Y) = Values'Old (X) and then
           (for all J in Values'Range =>
               (if J /= X and J /= Y then Values (J) = Values'Old (J)))
   is
      Temp : Integer;
   begin
      Temp       := Values (X);
      Values (X) := Values (Y);
      Values (Y) := Temp;
   end Swap;


   -- Finds the smallest element in the remaining unsorted data
   function Index_Of_Minimum (Unsorted : in Array_Type) return Positive
     with
       Pre =>
         Unsorted'First <= Unsorted'Last and then
         Unsorted'Last  <  Positive'Last,
       Post =>
         Index_Of_Minimum'Result in Unsorted'Range and then
         (for all J in Unsorted'Range =>
            Unsorted (Index_Of_Minimum'Result) <= Unsorted (J))
   is
      Min : Positive;
   begin
      Min := Unsorted'First;
      for Index in Positive range Unsorted'First + 1 .. Unsorted'Last loop
         pragma Loop_Invariant
           (Min in Unsorted'Range and then
              (for all J in Positive range Unsorted'First .. Index - 1 =>
                   Unsorted (Min) <= Unsorted (J)));

         if Unsorted (Index) < Unsorted (Min) then
            Min := Index;
         end if;
      end loop;
      return Min;
   end Index_Of_Minimum;


   procedure Selection_Sort (Values : in out Array_Type) is
      Smallest : Positive;  -- Index of the smallest value in the unsorted part
   begin -- Selection_Sort
      for Current in Values'First .. Values'Last - 1 loop
         Smallest := Index_Of_Minimum (Values (Current .. Values'Last));
         if Smallest /= Current then
            Swap (X   => Current,
                  Y   => Smallest,
                  Values => Values);
         end if;
         pragma Loop_Invariant
           (Current >= Values'First and then
            Current <  Values'Last  and then
            (for all J in Positive range Values'First .. Current - 1 =>
               Values (J) <= Values (J + 1)) and then
            (for all J in Positive range Current .. Values'Last =>
               Values (Current) <= Values (J)));
      end loop;

   end Selection_Sort;

end Sorters;
