pragma SPARK_Mode (On);

package Binary_Search is

   type T is range 0 .. 10000;
   subtype U is T range 1 .. 10000;

   type Ar is array (U) of Integer;

   function Search (A : Ar ; I : Integer) return T with
     Pre  => (for all I1 in A'Range =>
                (for all I2 in I1 .. A'Last =>
                   A (I1) <= A (I2))),
     Post => (if Search'Result in A'Range then A (Search'Result) = I
              else (for all Index in A'Range => A (Index) /= I));

end Binary_Search;
