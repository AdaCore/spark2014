procedure Exceptions_Post with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   Overflow : exception;
   Index    : Positive;

   procedure Incr_All_Post (A : aliased in out Nat_Array) with
     Post =>
       (for all I in A'Range => A'Old (I) /= Natural'Last
          and then A (I) = A'Old (I) + 1),
     Exceptional_Cases =>
       (Overflow => A'Old (Index) = Natural'Last
        and then (for all I in A'Range =>
                        A (I) = (if I < Index then A'Old (I) + 1 else A'Old (I))));

   procedure Incr_All_Post (A : aliased in out Nat_Array) is
   begin
      for I in A'Range loop
         if A (I) = Natural'Last then
            Index := I;
            raise Overflow;
         end if;

         A (I) := A (I) + 1;
         pragma Loop_Invariant
           (for all J in A'First .. I => A'Loop_Entry (J) < Natural'Last);
         pragma Loop_Invariant
           (for all J in A'First .. I => A (J) = A'Loop_Entry (J) + 1);
      end loop;
   end Incr_All_Post;

begin
   null;
end Exceptions_Post;
