procedure Exceptions_RTE with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   procedure Incr_All_CE (A : in out Nat_Array) with
     Post =>
       (for all I in A'Range => A'Old (I) /= Natural'Last
          and then A (I) = A'Old (I) + 1),
     Exceptional_Cases => (Constraint_Error => True);

   procedure Incr_All_CE (A : in out Nat_Array) is
   begin
      for I in A'Range loop
         A (I) := A (I) + 1;
         pragma Loop_Invariant
           (for all J in A'First .. I => A'Loop_Entry (J) < Natural'Last);
         pragma Loop_Invariant
           (for all J in A'First .. I => A (J) = A'Loop_Entry (J) + 1);
      end loop;
   end Incr_All_CE;

begin
   null;
end Exceptions_RTE;
