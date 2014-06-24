with Perm; use Perm;

package Sort with SPARK_Mode is
   subtype Array_Type is Nat_Array (1 .. 100);

   -- Sorts the elements in the array Values in ascending order
   procedure Selection_Sort (Values : in out Array_Type)
     with
       Post => Is_Perm (Values'Old, Values);
end Sort;
