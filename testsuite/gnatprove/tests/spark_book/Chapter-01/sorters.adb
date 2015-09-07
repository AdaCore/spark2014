pragma Spark_Mode (On);
package body Sorters is

   function Perm_Transitive (A, B, C : Array_Type) return Boolean
     with Global => null,
          Post   => (if Perm_Transitive'Result
                        and then Perm (A, B)
                        and then Perm (B, C)
                     then Perm (A, C)),
          Ghost   => True,
          Import  => True;


   procedure Swap (Values : in out Array_Type;
                   X      : in     Positive;
                   Y      : in     Positive)
     with Depends => (Values => (Values, X, Y)),
          Pre     => (X in Values'Range and then
                      Y in Values'Range and then
                      X /= Y),
          Post => Perm (Values'Old, Values)    and then
                  (Values (X) = Values'Old (Y) and then
                   Values (Y) = Values'Old (X) and then
                   (for all J in Values'Range =>
                      (if J /= X and J /= Y then Values (J) = Values'Old (J))))
   is
      Values_Old : constant Array_Type := Values
        with Ghost => True;
      Temp : Integer;
   begin
      Temp       := Values (X);
      Values (X) := Values (Y);
      Values (Y) := Temp;
      pragma Assume (Perm (Values_Old, Values));
   end Swap;


   -- Finds the index of the smallest element in the array
   function Index_Of_Minimum (Unsorted : in Array_Type) return Positive
     with Pre  => Unsorted'First <= Unsorted'Last,
          Post => Index_Of_Minimum'Result in Unsorted'Range and then
                 (for all J in Unsorted'Range =>
                  Unsorted (Index_Of_Minimum'Result) <= Unsorted (J))
   is
      Min : Positive;
   begin
      Min := Unsorted'First;
      for Index in Unsorted'First .. Unsorted'Last loop
         pragma Loop_Invariant
           (Min in Unsorted'Range and then
           (for all J in Unsorted'First .. Index - 1 =>
              Unsorted (Min) <= Unsorted (J)));

         if Unsorted (Index) < Unsorted (Min) then
            Min := Index;
         end if;
      end loop;
      return Min;
   end Index_Of_Minimum;


   procedure Selection_Sort (Values : in out Array_Type) is
      Values_Last : Array_Type (Values'Range)
        with Ghost => True;
      Smallest : Positive;  -- Index of the smallest value in the unsorted part
   begin -- Selection_Sort
      pragma Assume (Perm (Values, Values));
      for Current in Values'First .. Values'Last - 1 loop
         Values_Last := Values;
         Smallest := Index_Of_Minimum (Values (Current .. Values'Last));

         if Smallest /= Current then
            Swap (Values => Values,
                  X      => Current,
                  Y      => Smallest);
         end if;

         pragma Assume (Perm_Transitive (Values'Loop_Entry, Values_Last, Values));

         pragma Loop_Invariant (Perm (Values'Loop_Entry, Values));
         pragma Loop_Invariant   -- Simple partition property
           ((for all J in Current .. Values'Last =>
                 Values (Current) <= Values (J)));
         pragma Loop_Invariant  -- order property
           ((for all J in Values'First .. Current =>
               Values (J) <= Values (J + 1)));
      end loop;
   end Selection_Sort;
end Sorters;
