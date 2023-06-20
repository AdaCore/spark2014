procedure Exceptions_Bad_Init with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   Overflow : exception;
   Index    : Positive;

   procedure Incr_All (A : in out Nat_Array) with
     Import,
     Global => (In_Out => Index),
     Always_Terminates,
     Post =>
       (for all I in A'Range => A'Old (I) /= Natural'Last
          and then A (I) = A'Old (I) + 1),
     Exceptional_Cases =>
       (Overflow => Index in A'Old'Range and then A'Old (Index) = Natural'Last);

   procedure Incr_All_Bad_Init
     (A       : in out Nat_Array;
      Success : out Boolean;
      N       : out Natural)
   with
     Post => Success = (for all I in A'Range => A'Old (I) /= Natural'Last)
       and then
         (if Success then (for all I in A'Range => A (I) = A'Old (I) + 1));

   procedure Incr_All_Bad_Init
     (A       : in out Nat_Array;
      Success : out Boolean;
      N       : out Natural)
   is
   begin
      Incr_All (A);
      Success := True;
      N := 0;
   exception
      when Overflow =>
         Success := False;
         N := A (Index);
   end Incr_All_Bad_Init;

begin
   null;
end Exceptions_Bad_Init;
