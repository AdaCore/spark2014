package Binary_Search
  with SPARK_Mode
is
   ----------------------------------------------------
   --     SPARK 2014 - Binary_Search Example         --
   --                                                --
   -- This example illustrates the specification of  --
   -- a simple search function.                      --
   ----------------------------------------------------


   type T is range 0 .. 10;
   subtype U is T range 1 .. 10;

   type Ar is array (U) of Integer;

   function Search (A : Ar; I : Integer) return T with
     -- A is sorted
     Pre  => (for all I1 in A'Range =>
                (for all I2 in I1 .. A'Last =>
                   A (I1) <= A (I2))),
     -- If I exists in A, then Search'Result indicates its position
     Post => (if Search'Result in A'Range then A (Search'Result) = I
              else (for all Index in A'Range => A (Index) /= I));

end Binary_Search;
