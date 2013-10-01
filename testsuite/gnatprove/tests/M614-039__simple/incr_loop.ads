package Incr_Loop is

   type Arr_Type is array (Integer range <>) of Integer;

   procedure Iter (A : in out Arr_Type)
      with Pre => (for all I in A'Range => A (I) < Integer'Last),
           Post =>
            (A'Last = A'Last'Old and
             (for all I in A'Range => A( I) = A'Old (I) + 1));

end Incr_Loop;
