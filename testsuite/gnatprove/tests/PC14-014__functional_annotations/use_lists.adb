pragma Ada_2012;
package body Use_Lists with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   function My_Find (L : List; E : Element_Type) return Cursor is
      Cu : Cursor := First (L);
   begin
      while Has_Element (L, Cu) loop
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (L), Cu) - 1 =>
              Element (Model (L), I) /= E);
         if Element (L, Cu) = E then
            return Cu;
         end if;
         Next (L, Cu);
      end loop;
      return No_Element;
   end My_Find;

   procedure Incr_All (L1 : List; L2 : in out List) is
      Cu : Cursor := First (L1);
   begin
      Clear (L2);
      while Has_Element (L1, Cu) loop
         pragma Loop_Invariant
           (for all N in 1 .. Length (L2) =>
                Is_Incr (Element (Model (L1), N), Element (Model (L2), N)));
         pragma Loop_Invariant (P.Get (Positions (L1), Cu) = Length (L2) + 1);
         if Element (L1, Cu) < Element_Type'Last then
            Append (L2, Element (L1, Cu) + 1);
         else
            Append (L2, Element (L1, Cu));
         end if;
         Next (L1, Cu);
      end loop;
   end Incr_All;

   procedure Incr_All_2 (L : in out List) is
      Cu : Cursor := First (L);
   begin
      while Has_Element (L, Cu) loop
         pragma Loop_Invariant (Length (L) = Length (L)'Loop_Entry);
         pragma Loop_Invariant
           (for all N in 1 .. P.Get (Positions (L), Cu) - 1 =>
                Is_Incr (Element (Model (L)'Loop_Entry, N),
                         Element (Model (L), N)));
         pragma Loop_Invariant
           (for all N in P.Get (Positions (L), Cu) .. Length (L) =>
                Element (Model (L)'Loop_Entry, N) =
                Element (Model (L), N));
         if Element (L, Cu) < Element_Type'Last then
            Replace_Element (L, Cu, Element (L, Cu) + 1);
         end if;
         Next (L, Cu);
      end loop;
   end Incr_All_2;

   procedure Incr_All_3 (L : in out List) is
      Cu : Cursor := First (L);
   begin
      while Has_Element (L, Cu) loop
         pragma Loop_Invariant (Length (L) = Length (L)'Loop_Entry);
         pragma Loop_Invariant
           (for all N in 1 .. P.Get (Positions (L), Cu) - 1 =>
                Is_Incr (Element (Model (L)'Loop_Entry, N),
                         Element (Model (L), N)));
         pragma Loop_Invariant
           (for all N in P.Get (Positions (L), Cu) .. Length (L) =>
                Element (Model (L)'Loop_Entry, N) =
                Element (Model (L), N));
         pragma Loop_Invariant (Positions (L)'Loop_Entry =
                                  Positions (L));
         if Element (L, Cu) < Element_Type'Last then
            Replace_Element (L, Cu, Element (L, Cu) + 1);
         end if;
         Next (L, Cu);
      end loop;
   end Incr_All_3;

   procedure Double_Size (L : in out List) is
      Cu   : Cursor := First (L);
      Lgth : Count_Type := Length (L);
   begin
      for I in 1 .. Lgth loop
         pragma Loop_Invariant (Has_Element (L, Cu));
         pragma Loop_Invariant (Length (L) = Length (L)'Loop_Entry + I - 1);
         pragma Loop_Invariant
           (for all I in 1 .. Length (L)'Loop_Entry =>
                Element (Model (L), I) =
              Element (Model (L)'Loop_Entry, I));
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 =>
              Element (Model (L), J + Length (L)'Loop_Entry) =
                Element (Model (L)'Loop_Entry, J));
         pragma Loop_Invariant
           (P.Get (Positions (L), Cu) = I);
         Append (L, Element (L, Cu));
         Next (L, Cu);
      end loop;
   end Double_Size;

   procedure Double_Size_2 (L : in out List) is
      Cu : Cursor := First (L);
      N  : Count_Type := 0 with Ghost;
   begin
      while Has_Element (L, Cu) loop
         pragma Loop_Invariant (Length (L) = Length (L)'Loop_Entry + N);
         pragma Loop_Invariant
           (for all I in 1 .. N =>
              Element (Model (L), 2 * I) = Element (Model (L)'Loop_Entry, I)
            and Element (Model (L), 2 * I - 1) =
                Element (Model (L)'Loop_Entry, I));
         pragma Loop_Invariant
           (for all I in N + 1 .. Length (L)'Loop_Entry =>
                Element (Model (L), I + N) =
                Element (Model (L)'Loop_Entry, I));
         pragma Loop_Invariant (P.Get (Positions (L), Cu) = 2 * N + 1);
         Insert (L, Cu, Element (L, Cu));
         Next (L, Cu);
         N := N + 1;
      end loop;
   end Double_Size_2;

   procedure Update_Range_To_Zero (L : in out List; Fst, Lst : Cursor) is
      Current : Cursor := Fst;
      N_Last  : Cursor := Lst;
   begin
      Next (L, N_Last);
      while Current /= N_Last loop
         pragma Loop_Invariant (Length (L) = Length (L)'Loop_Entry);
         pragma Loop_Invariant (Positions (L) =
                                  Positions (L)'Loop_Entry);
         pragma Loop_Invariant (P.Has_Key (Positions (L), Current));
         pragma Loop_Invariant
           (P.Get (Positions (L), Current) in
              P.Get (Positions (L), Fst) .. P.Get (Positions (L), Lst));
         pragma Loop_Invariant
           (for all I in
              P.Get (Positions (L), Fst) .. P.Get (Positions (L), Current) - 1
            =>
                Element (Model (L), I) = 0);
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (L), Fst) - 1 =>
              Element (Model (L), I) =
              Element (Model (L)'Loop_Entry, I));
         pragma Loop_Invariant
           (for all I in P.Get (Positions (L), Current) .. Length (L) =>
              Element (Model (L), I) =
              Element (Model (L)'Loop_Entry, I));
         Replace_Element (L, Current, 0);
         Next (L, Current);
      end loop;
   end Update_Range_To_Zero;

   procedure Insert_Count (L : in out List; Cu : Cursor) is
   begin
      Insert (L, Cu, 0);
      Insert (L, Cu, 0);
      Insert (L, Cu, 0);
      Insert (L, Cu, 0);
      Insert (L, Cu, 0);
      Insert (L, Cu, 0);
      Insert (L, Cu, 0);
   end Insert_Count;

   function Prop (E : Element_Type) return Boolean is
   begin
      return E >= 0;
   end Prop;

   procedure From_Higher_To_Lower (L : List) is null;

   procedure From_Lower_To_Higher (L : List) is
   begin
      Lift_Abstraction_Level (L);
   end From_Lower_To_Higher;

end Use_Lists;
