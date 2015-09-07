package Sorted_Arrays is
   type Integer_Array is array(Positive range <>) of Integer;

   -- Sorts the given array.
   procedure Sort (Data : in out Integer_Array)
     with Global => null,
          Post   => (for all J in Data'First .. Data'Last - 1 =>
                        (Data(J) <= Data(J + 1)));

   -- Return index of specified Value if it exists; zero if Value not in Data.
   function Binary_Search (Data  : in Integer_Array;
                           Value : in Integer) return Natural
     with Pre => (for all J in Data'First .. Data'Last - 1 =>
                     (Data(J) <= Data(J + 1)));
end Sorted_Arrays;
