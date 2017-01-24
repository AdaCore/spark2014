package body Int_List is pragma SPARK_Mode (On);
   procedure Add (L : in out List; I : My_Int) is
   begin
      Prepend (L, I);
   end Add;

   procedure Incr (L : in out List) is
      C    : Cursor := First (L);
   begin
      while Has_Element (L, C) loop
         pragma Loop_Invariant
           (Length (L) = Length (L'Loop_Entry));
         pragma Loop_Invariant (Positions (L) = Positions (L)'Loop_Entry);
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (L), C) - 1 =>
              Element (Model (L), I) = Element (Model (L'Loop_Entry), I) + 1);
         pragma Loop_Invariant
           (for all I in P.Get (Positions (L), C) .. Length (L) =>
              Element (Model (L), I) = Element (Model (L'Loop_Entry), I));
         Replace_Element (L, C, Element (L, C) + 1);
         Next (L, C);
      end loop;
   end Incr;
end Int_List;
