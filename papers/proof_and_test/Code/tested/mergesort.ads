package Mergesort is
  Min_Table_Size : constant := 1;
  Max_Table_Size : constant := 5;

  subtype Index_Range is Integer range Min_Table_Size .. Max_Table_Size;
  type    Our_Array   is array (Index_Range) of Integer;

  procedure Merge (A                   : in     Our_Array;
                   ILeft, IRight, IEnd : in     Integer;
                   B                   : in out Our_Array);

  procedure Merge_Sort (A : in out Our_Array);
  --  Sorts the elements of array A into ascending order.
end Mergesort;
