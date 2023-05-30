procedure Exceptions with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   Overflow : exception;
   Index    : Positive;

   procedure Incr_All (A : in out Nat_Array) with
     Post =>
       (for all I in A'Range => A'Old (I) /= Natural'Last
          and then A (I) = A'Old (I) + 1),
     Exceptional_Cases =>
       (Overflow => Index in A'Old'Range and then A'Old (Index) = Natural'Last);

   procedure Incr_All (A : in out Nat_Array) is
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
   end Incr_All;

   procedure Incr_All_Cond (A : in out Nat_Array; Success : out Boolean) with
     Post => Success = (for all I in A'Range => A'Old (I) /= Natural'Last)
       and then
         (if Success then (for all I in A'Range => A (I) = A'Old (I) + 1));

   procedure Incr_All_Cond (A : in out Nat_Array; Success : out Boolean) is
   begin
      Incr_All (A);
      Success := True;
   exception
      when Overflow =>
	 A := (others => 0);
         Success := False;
   end Incr_All_Cond;

   procedure Incr_All_With_Pre (A : in out Nat_Array) with
     Pre  => (for all I in A'Range => A (I) /= Natural'Last),
     Post =>
       (for all I in A'Range => A'Old (I) /= Natural'Last
          and then A (I) = A'Old (I) + 1);

   procedure Incr_All_With_Pre (A : in out Nat_Array) is
   begin
      Incr_All (A);
   end Incr_All_With_Pre;

begin
   null;
end Exceptions;
