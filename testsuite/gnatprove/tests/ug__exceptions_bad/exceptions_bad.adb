procedure Exceptions_Bad with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   Overflow : exception;
   Index    : Positive;

   procedure Incr_All_Bad (A : in out Nat_Array) with
     Import,
     Post =>
       (for all I in A'Range => A'Old (I) /= Natural'Last
          and then A (I) = A'Old (I) + 1),
     Exceptional_Cases =>
       (Overflow => A'Old (Index) = Natural'Last
        and then (for all I in A'Range =>
                        A (I) = (if I < Index then A'Old (I) + 1 else A'Old (I))));

begin
   null;
end Exceptions_Bad;
