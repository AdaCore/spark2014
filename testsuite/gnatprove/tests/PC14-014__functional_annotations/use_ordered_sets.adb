package body Use_Ordered_Sets with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   function My_Find (S : My_Sets.Set; E : Element_Type) return Cursor is
      Cu : Cursor := First (S);
   begin
      while Has_Element (S, Cu) loop
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (S), Cu) - 1 =>
              Formal_Model.E.Get (Elements (S), I) /= E);
         if Element (S, Cu) = E then
            return Cu;
         end if;
         Cu := Next (S, Cu);
      end loop;
      return No_Element;
   end My_Find;

   procedure Apply_F (S : My_Sets.Set; R : in out My_Sets.Set) is
      Cu : Cursor := First (S);
   begin
      Clear (R);
      while Has_Element (S, Cu) loop
         pragma Loop_Invariant (Length (R) <= P.Get (Positions (S), Cu) - 1);
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (S), Cu) - 1 =>
              Contains (R, F (E.Get (Elements (S), I))));
         pragma Loop_Invariant
           (for all G of Model (R) =>
              (for some I in 1 .. P.Get (Positions (S), Cu) - 1 =>
                   G = F (E.Get (Elements (S), I))));
         Include (R, F (Element (S, Cu)));
         Cu := Next (S, Cu);
      end loop;
   end Apply_F;

   function Are_Disjoint (S1, S2 : My_Sets.Set) return Boolean is
      Cu : Cursor := First (S1);
   begin
      while Has_Element (S1, Cu) loop
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (S1), Cu) - 1 =>
              not Contains (S2, E.Get (Elements (S1), I)));
         if Contains (S2, Element (S1, Cu)) then
            return False;
         end if;
         Cu := Next (S1, Cu);
      end loop;
      return True;
   end Are_Disjoint;

   function Are_Disjoint_2 (S1, S2 : My_Sets.Set) return Boolean is
      Cu : Cursor := First (S1);
   begin
      while Has_Element (S1, Cu) loop
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (S1), Cu) - 1 =>
              not M.Contains (Model (S2), E.Get (Elements (S1), I)));
         if Contains (S2, Element (S1, Cu)) then
            return False;
         end if;
         Cu := Next (S1, Cu);
      end loop;
      return True;
   end Are_Disjoint_2;

   procedure Union_Prop (S1 : in out My_Sets.Set; S2 : My_Sets.Set) is
   begin
      Union (S1, S2);
   end Union_Prop;

   procedure Move (S1, S2 : in out My_Sets.Set) is
      Cu : Cursor := First (S1);
   begin
      Clear (S2);
      while Has_Element (S1, Cu) loop
         pragma Loop_Invariant
           (Length (S1) = Length (S1)'Loop_Entry - Length (S2));
         pragma Loop_Invariant (Model (S2) <= Model (S1)'Loop_Entry);
         pragma Loop_Invariant (Model (S1) <= Model (S1)'Loop_Entry);
         pragma Loop_Invariant
           (M.Included_In_Union
              (Model (S1)'Loop_Entry, Model (S2), Model (S1)));
         pragma Loop_Invariant
           (M.Is_Empty (M.Intersection (Model (S1), Model (S2))));
         Include (S2, Element (S1, Cu));
         Exclude (S1, Element (S1, Cu));
         Cu := First (S1);
      end loop;
   end Move;

   procedure Move_2 (S1, S2 : in out My_Sets.Set) is
      Cu : Cursor := First (S1);
   begin
      Clear (S2);
      while Has_Element (S1, Cu) loop
         pragma Loop_Invariant (P.Get (Positions (S1), Cu) = 1);
         pragma Loop_Invariant
           (Length (S1) = Length (S1)'Loop_Entry - Length (S2));
         pragma Loop_Invariant
           (for all I in 1 .. Length (S2) =>
                E.Get (Elements (S2), I) = E.Get (Elements (S1)'Loop_Entry, I));
         pragma Loop_Invariant
           (for all I in 1 .. Length (S1) =>
                E.Get (Elements (S1), I) =
                E.Get (Elements (S1)'Loop_Entry, Length (S2) + I));
         Include (S2, Element (S1, Cu));
         Exclude (S1, Element (S1, Cu));
         Cu := First (S1);
      end loop;
   end Move_2;

   procedure Move_3 (S1, S2 : in out My_Sets.Set) is
      Cu : Cursor := First (S1);
   begin
      Clear (S2);
      while Has_Element (S1, Cu) loop
         pragma Loop_Invariant (P.Get (Positions (S1), Cu) = Length (S2) + 1);
         pragma Loop_Invariant
           (for all I in 1 .. Length (S2) =>
                M.Contains (Model (S2), E.Get (Elements (S1), I)));
         pragma Loop_Invariant
           (for all E of Model (S2) =>
                (for some I in 1 .. Length (S2) =>
                       Formal_Model.E.Get (Elements (S1), I) = E));
         Include (S2, Element (S1, Cu));
         Cu := Next (S1, Cu);
      end loop;
      Clear (S1);
   end Move_3;

   procedure Move_4 (S1, S2 : in out My_Sets.Set) is
      Cu : Cursor := First (S1);
   begin
      Clear (S2);
      while Has_Element (S1, Cu) loop
         pragma Loop_Invariant (P.Get (Positions (S1), Cu) = Length (S2) + 1);
         pragma Loop_Invariant
           (for all I in 1 .. Length (S2) =>
                E.Get (Elements (S2), I) = E.Get (Elements (S1), I));
         Include (S2, Element (S1, Cu));
         Cu := Next (S1, Cu);
      end loop;
      Clear (S1);
   end Move_4;

   procedure Double_Size (S : in out My_Sets.Set) is
      Cu : Cursor := First (S);
      N  : Count_Type := 0 with Ghost;
   begin
      while Has_Element (S, Cu) loop
         pragma Loop_Invariant (Length (S) = Length (S)'Loop_Entry + N);
         pragma Loop_Invariant
           (for all I in 1 .. N =>
            E.Get (Elements (S), 2 * I) = E.Get (Elements (S)'Loop_Entry, I) + 1
            and E.Get (Elements (S), 2 * I - 1) =
              E.Get (Elements (S)'Loop_Entry, I));
         pragma Loop_Invariant
           (for all I in 2 * N + 1 .. Length (S) =>
                E.Get (Elements (S), I) =
              E.Get (Elements (S)'Loop_Entry, I - N));
         pragma Loop_Invariant (P.Get (Positions (S), Cu) = 2 * N + 1);
         pragma Assert (not Contains (S, Element (S, Cu) + 1));
         Include (S, Element (S, Cu) + 1);
         Cu := Next (S, Next (S, Cu));
         N := N + 1;
      end loop;
   end Double_Size;

   procedure Insert_Count (S : in out My_Sets.Set) is
   begin
      Include (S, 1);
      Include (S, 2);
      Include (S, 3);
      Include (S, 4);
      Include (S, 5);
   end Insert_Count;

   function Q (E : Element_Type) return Boolean is
   begin
      return E >= 0;
   end Q;

   procedure From_Elements_To_Model (S : My_Sets.Set) is null;

   procedure From_Model_To_Elements (S : My_Sets.Set) is null;

   procedure From_Elements_To_Cursors (S : My_Sets.Set) is null;

   procedure From_Cursors_To_Elements (S : My_Sets.Set) is
   begin
      Lift_Abstraction_Level (S);
   end From_Cursors_To_Elements;

   procedure From_Model_To_Cursors (S : My_Sets.Set) is null;

   procedure From_Cursors_To_Model (S : My_Sets.Set)  is
   begin
      Lift_Abstraction_Level (S);
   end From_Cursors_To_Model;

end Use_Ordered_Sets;
