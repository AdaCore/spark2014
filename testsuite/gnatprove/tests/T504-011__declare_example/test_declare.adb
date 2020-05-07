procedure Test_Declare with SPARK_Mode is

   type My_Array is array (Positive range <>) of Integer;

   function Has_Zero (A : My_Array) return Boolean is
     (for some E of A => E = 0);

   function Has_Two_Zeros (A : My_Array) return Boolean is
     (for some I in A'Range => A (I) = 0 and
        (for some J in A'Range => A (J) = 0 and I /= J));

   function Find_First_Zero (A : My_Array) return Natural with
     Pre  => Has_Zero (A),
     Post => Find_First_Zero'Result in A'Range
     and A (Find_First_Zero'Result) = 0
     and not Has_Zero (A (A'First .. Find_First_Zero'Result - 1))
   is
   begin
      for I in A'Range loop
         if A (I) = 0 then
            return I;
         end if;

         pragma Loop_Invariant (not Has_Zero (A (A'First .. I)));
      end loop;

      raise Program_Error;
   end Find_First_Zero;

   procedure Set_Range_To_Zero (A : in out My_Array) with
     Pre  => Has_Two_Zeros (A),
     Post =>
       (declare
          Fst_Zero : constant Positive := Find_First_Zero (A'Old);
          Snd_Zero : constant Positive := Find_First_Zero
            (A'Old (Fst_Zero + 1 .. A'Last));
        begin
          A = (A'Old with delta Fst_Zero .. Snd_Zero => 0))
   is
      Fst_Zero : Positive := 1 with Ghost;
      Found    : Boolean := False;
   begin
      for I in A'Range loop
         if A (I) = 0 then
            exit when Found;

            Found := True;
            Fst_Zero := I;
         elsif Found then
            A (I) := 0;
         end if;

         pragma Loop_Invariant
           (if Found then Fst_Zero = Find_First_Zero (A'Loop_Entry)
            else not Has_Zero (A (A'First .. I)));
         pragma Loop_Invariant
           (if Found then Fst_Zero <= I
              and not Has_Zero (A'Loop_Entry (Fst_Zero + 1 .. I)));
         pragma Loop_Invariant
           (if Found then A = (A'Loop_Entry with delta Fst_Zero .. I => 0)
            else A = A'Loop_Entry);
      end loop;
   end Set_Range_To_Zero;
begin
   null;
end Test_Declare;
