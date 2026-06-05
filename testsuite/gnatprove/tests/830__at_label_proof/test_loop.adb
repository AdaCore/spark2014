pragma Extensions_Allowed (All_Extensions);

procedure Test_Loop with SPARK_Mode
is

   Max_Size : constant := 1024;

   type Int32 is range 0 .. 2**31 - 1;
   subtype Length is Int32 range 0 .. Max_Size;

   subtype Index is Length range 1 .. Max_Size;

   type Buffer is array (Index range <>) of Character;

   type Counts_Array is array (Character) of Length;

   function Sum (Arr : Counts_Array; Up_To : Character) return Int32
   is (if Up_To = Character'First
       then Arr (Up_To)
       else Arr (Up_To) + Sum (Arr, Character'Pred (Up_To)))
     with
       Ghost,
       Subprogram_Variant => (Decreases => Up_To),
       Post               =>
         Sum'Result <= Length'Last * (Character'Pos (Up_To) + 1);

   function Sum (Arr : Counts_Array) return Int32
   is (Sum (Arr, Character'Last))
     with Ghost;

   procedure Lem_Sum_Zero (Arr : Counts_Array; Up_To : Character)
     with
       Ghost,
       Global             => null,
       Subprogram_Variant => (Decreases => Up_To),
       Pre                =>
         (for all C in Character'First .. Up_To => Arr (C) = 0),
         Post               => Sum (Arr, Up_To) = 0;

   procedure Lem_Sum_Zero (Arr : Counts_Array; Up_To : Character) is
   begin
      if Up_To /= Character'First then
         Lem_Sum_Zero (Arr, Character'Pred (Up_To));
      end if;
   end Lem_Sum_Zero;

   procedure Lem_Incr_Def (A1, A2 : Counts_Array; Up_To, Pos : Character)
     with
       Ghost,
       Global             => null,
       Subprogram_Variant => (Decreases => Up_To),
       Pre                =>
         (for all C in Character =>
                 (if C /= Pos then A1 (C) = A2 (C))),
       Post               => Sum (A2, Up_To) =
           (if Pos <= Up_To then Sum (A1, Up_To) - A1 (Pos) + A2 (Pos)
              else Sum (A1, Up_To));

   procedure Lem_Incr_Def (A1, A2 : Counts_Array; Up_To, Pos : Character) is
   begin
      if Up_To /= Character'First then
         Lem_Incr_Def (A1, A2, Character'Pred (Up_To), Pos);
      end if;
   end Lem_Incr_Def;

   function Char_Counts (Input : Buffer) return Counts_Array with
     Post => (for all C in Character =>
                Char_Counts'Result (C) <= Input'Length)
       and Sum (Char_Counts'Result) = Input'Length;

   function Char_Counts (Input : Buffer) return Counts_Array is
      Counts : Counts_Array := [others => 0];
   begin
      Lem_Sum_Zero (Counts, Character'Last);
      for I in Input'Range loop
         <<Before>>
         Counts (Input (I)) := Counts (Input (I)) + 1;
         Lem_Incr_Def (Counts'At (Before), Counts, Character'Last, Input (I));
         pragma Loop_Invariant (for all C in Character =>
                                  Counts (C) <= I - Input'First + 1);
         pragma Loop_Invariant (Sum (Counts) = I - Input'First + 1);
      end loop;
      return Counts;
   end Char_Counts;

begin
   null;
end;
