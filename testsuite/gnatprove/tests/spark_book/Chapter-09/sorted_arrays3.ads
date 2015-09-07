package Sorted_Arrays3 is
   type Integer_Array is array(Positive range <>) of Integer;

   function Is_Sorted (Data : in Integer_Array) return Boolean
   is (for all J in Data'First .. Data'Last - 1 =>
         (Data(J) <= Data(J + 1)))
     with Ghost  => True;

   -- Sorts the given array.
   procedure Sort (Data : in out Integer_Array)
     with Global => null,
          Post   => Is_Sorted (Data);

   -- Return index of specified Value if it exists; zero if Value not in Data.
   function Binary_Search (Data  : in Integer_Array;
                           Value : in Integer) return Natural
     with Pre => Is_Sorted (Data);

end Sorted_Arrays3;
