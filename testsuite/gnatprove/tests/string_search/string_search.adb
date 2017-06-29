package body String_Search
  with SPARK_Mode
is
   function Brute_Force (Needle, Haystack : in Text) return Natural is
      Diff : Boolean;
   begin
      for I in 1 .. Haystack'Length - Needle'Length + 1 loop
         Diff := False;

         for J in Needle'Range loop
            Diff := Needle(J) /= Haystack(J + (I - 1));
            exit when Diff;
            pragma Loop_Invariant (Partial_Match_At (Needle, Haystack, I, J));
            pragma Loop_Invariant (Diff = (Needle(J) /= Haystack(J + (I - 1))));
         end loop;

         if not Diff then
            return I;
         end if;

         pragma Loop_Invariant
           (for all K in 1 .. I => not Match_At (Needle, Haystack, K));
      end loop;

      return 0;
   end Brute_Force;

   function Brute_Force_Slice (Needle, Haystack : in Text) return Natural is
   begin
      for I in 1 .. Haystack'Length - Needle'Length + 1 loop
         if Needle = Haystack(I .. I + (Needle'Last - 1)) then
            return I;
         end if;

         pragma Loop_Invariant
           (for all K in 1 .. I => not Match_At (Needle, Haystack, K));
      end loop;

      return 0;
   end Brute_Force_Slice;

   procedure Make_Bad_Shift (Needle : Text; Bad_Shift : out Shift_Table) is
   begin
      Bad_Shift := (others => Needle'Length + 1);

      for J in Needle'Range loop
         Bad_Shift(Needle(J)) := Needle'Length - J + 1;
         pragma Loop_Invariant (for all C in Character => Bad_Shift(C) in 1 .. Needle'Length + 1);
         pragma Loop_Invariant (for all C in Character =>
                                  (if Bad_Shift(C) = Needle'Length + 1 then
                                     (for all K in 1 .. J => C /= Needle(K))
                                   else
                                      Needle(Needle'Length - Bad_Shift(C) + 1) = C
                                      and (for all K in Needle'Length - Bad_Shift(C) + 2 .. J => Needle(K) /= C)
                                ));
      end loop;
   end Make_Bad_Shift;

   function QS (Needle, Haystack : in Text) return Natural is
      Bad_Shift : Shift_Table;
      I : Positive;

      procedure Prove_QS with Ghost is
         Shift : constant Positive := Bad_Shift(Haystack(I + Needle'Length));
      begin
         for K in I + 1 .. I + Shift - 1 loop
            pragma Assert (Haystack(I + Needle'Length) /= Needle(I + Needle'Length - K + 1));
            pragma Loop_Invariant
              (for all L in 1 .. K => not Match_At (Needle, Haystack, L));
         end loop;
      end Prove_QS;

   begin
      --  Preprocessing
      Make_Bad_Shift (Needle, Bad_Shift);

      --  Searching
      I := 1;
      while I <= Haystack'Length - Needle'Length + 1 loop
         if Needle = Haystack(I .. I + (Needle'Last - 1)) then
            return I;
         end if;
         exit when I = Haystack'Length - Needle'Length + 1;

         Prove_QS;

         pragma Loop_Variant (Increases => I);
         pragma Loop_Invariant (I <= Haystack'Length - Needle'Length);
         pragma Loop_Invariant
           (for all K in 1 .. I + Bad_Shift(Haystack(I + Needle'Length)) - 1 => not Match_At (Needle, Haystack, K));

         I := I + Bad_Shift(Haystack(I + Needle'Length));  --  Shift
      end loop;

      return 0;
   end QS;

end String_Search;
