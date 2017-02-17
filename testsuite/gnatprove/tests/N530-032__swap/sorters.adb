package body Sorters
   with SPARK_Mode
is

   procedure Swap (X : in out Integer;
                   Y : in out Integer)
   with
      Depends => (X => Y,
                  Y => X),
      Post => (X = Y'Old and then
               Y = X'Old)
   is
      Temp : Integer;
   begin
      Temp := X;
      X    := Y;
      Y    := Temp;
   end Swap;


   -- Finds the index of the smallest element in the array
   function Index_Of_Minimum (Unsorted : in Array_Type) return Positive
     with
       Pre =>
         Unsorted'First <= Unsorted'Last and then
         Unsorted'First <  Positive'Last,
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
         pragma Assert ((for all J in Positive range  Current .. Values'Last =>
                             Values (Smallest) <= Values (J)));
         if Smallest /= Current then
            Swap (X  => Values (Current),
                  Y  => Values (Smallest));
         end if;
         pragma Assert ((for all J in Positive range  Current .. Values'Last =>
                             Values (Current) <= Values (J)));

--           pragma Loop_Invariant
--             ((for all J in Positive range Current .. Values'Last =>
--                 Values (Current) <= Values (J)));
--           pragma Loop_Invariant
--             ((for all J in Positive range Values'First .. Current - 1 =>
--                 Values (J) <= Values (J + 1)));
      end loop;

   end Selection_Sort;

end Sorters;
