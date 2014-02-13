package Binary_Search
  with SPARK_Mode
is

   ------------------------------------------------------
   -- SPARK 2014 - Binary_Search_Unconstrained Example --
   --                                                  --
   -- This example illustrates the specification of    --
   -- a simple search function over an unconstrained   --
   -- array.                                           --
   --                                                  --
   -- Note the use of the Sorted expression function   --
   -- to define and express the precondition of Seach  --
   ------------------------------------------------------

   type Opt_Index is new Natural;

   subtype Index is Opt_Index range 1 .. Opt_Index'Last - 1;

   No_Index : constant Opt_Index := 0;

   type Ar is array (Index range <>) of Integer;

   function Empty (A : Ar) return Boolean is (A'First > A'Last);

   function Sorted (A : Ar) return Boolean is
      (for all I1 in A'Range =>
         (for all I2 in I1 .. A'Last => A (I1) <= A (I2)));

   function Search (A : Ar; I : Integer) return Opt_Index with
     Pre  => Sorted (A),
     Post => (if Search'Result in A'Range then A (Search'Result) = I
              else (for all Index in A'Range => A (Index) /= I));

end Binary_Search;
