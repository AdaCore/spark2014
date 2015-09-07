package body Sorted_Arrays2 is

   function Is_Sorted (Data : in Integer_Array) return Boolean is
   begin
      return (for all J in Data'First .. Data'Last - 1 =>
                (Data(J) <= Data(J + 1)));
   end Is_Sorted;


   -- Sorts the given array.
   procedure Sort (Data : in out Integer_Array) is
   begin
      null;  -- FIX ME!
   end Sort;


   -- Returns the index of the specified Value in Data if it exists; zero if Value does not exist in Data.
   function Binary_Search (Data : Integer_Array; Value : Integer) return Natural is
   begin
      return 0;  -- FIX ME!
   end Binary_Search;

end Sorted_Arrays2;
