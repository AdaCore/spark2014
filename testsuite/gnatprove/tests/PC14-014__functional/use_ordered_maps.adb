package body Use_Ordered_Maps with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   function My_Find (S : Map; K : Positive) return Cursor is
      Cu : Cursor := First (S);
   begin
      while Has_Element (S, Cu) loop
         pragma Loop_Variant (Increases => P.Get (Positions (S), Cu));
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (S), Cu) - 1 =>
              Formal_Model.K.Get (Keys (S), I) /= K);
         if Key (S, Cu) = K then
            return Cu;
         end if;
         Cu := Next (S, Cu);
      end loop;
      return No_Element;
   end My_Find;

   procedure Apply_F (S : Map; R : in out Map) is
      Cu : Cursor := First (S);
   begin
      Clear (R);
      while Has_Element (S, Cu) loop
         pragma Loop_Invariant (Length (R) = P.Get (Positions (S), Cu) - 1);
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (S), Cu) - 1 =>
              (for some K of R =>
                   Element (R, K) =
                   F (Element (S, Formal_Model.K.Get (Keys (S), I)))));
         pragma Loop_Invariant
           (for all K of R =>
                (for some I in 1 .. P.Get (Positions (S), Cu) - 1 =>
                     Element (R, K) =
                     F (Element (S, Formal_Model.K.Get (Keys (S), I)))));
         pragma Loop_Invariant
           (for all I in P.Get (Positions (S), Cu) .. Length (S) =>
                 not Contains (Model (R), K.Get (Keys (S), I)));
         Include (R, Key (S, Cu), F (Element (S, Cu)));
         Cu := Next (S, Cu);
      end loop;
   end Apply_F;

   procedure Apply_F_2 (S : Map; R : in out Map) is
      Cu : Cursor := First (S);
   begin
      Clear (R);
      while Has_Element (S, Cu) loop
         pragma Loop_Invariant (Length (R) = P.Get (Positions (S), Cu) - 1);
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (S), Cu) - 1 =>
              Contains (Model (R), K.Get (Keys (S), I))
            and then Element (R, K.Get (Keys (S), I)) =
                F (Element (S, K.Get (Keys (S), I))));
         pragma Loop_Invariant
           (for all K of R =>
                (for some I in 1 .. P.Get (Positions (S), Cu) - 1 =>
                     K = Formal_Model.K.Get (Keys (S), I)));
         Include (R, Key (S, Cu), F (Element (S, Cu)));
         Cu := Next (S, Cu);
      end loop;
   end Apply_F_2;

   procedure Apply_F_3 (S : in out Map) is
      Cu : Cursor := First (S);
   begin
      while Has_Element (S, Cu) loop
         pragma Loop_Invariant (Positions (S) = Positions (S)'Loop_Entry);
         pragma Loop_Invariant (Keys (S) = Keys (S)'Loop_Entry);
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (S), Cu) - 1 =>
              Element (S, K.Get (Keys (S), I)) =
                F (Element (Model (S)'Loop_Entry, K.Get (Keys (S), I))));
         pragma Loop_Invariant
           (for all I in P.Get (Positions (S), Cu) .. Length (S) =>
              Element (Model (S)'Loop_Entry, K.Get (Keys (S), I)) =
              Element (S, K.Get (Keys (S), I)));
         Include (S, Key (S, Cu), F (Element (S, Cu)));
         Cu := Next (S, Cu);
      end loop;
   end Apply_F_3;

   procedure Apply_F_4 (S : in out Map) is
      Cu : Cursor := First (S);
   begin
      while Has_Element (S, Cu) loop
         pragma Loop_Invariant (Positions (S) = Positions (S)'Loop_Entry);
         pragma Loop_Invariant (Keys (S) = Keys (S)'Loop_Entry);
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (S), Cu) - 1 =>
              Element (S, K.Get (Keys (S), I)) =
                F (Element (Model (S)'Loop_Entry, K.Get (Keys (S), I))));
         pragma Loop_Invariant
           (for all I in P.Get (Positions (S), Cu) .. Length (S) =>
              Element (Model (S)'Loop_Entry, K.Get (Keys (S), I)) =
                Element (S, K.Get (Keys (S), I)));
         Include (S, Key (S, Cu), F (Element (S, Cu)));
         Cu := Next (S, Cu);
      end loop;
   end Apply_F_4;

   function Are_Disjoint (S1, S2 : Map) return Boolean is
      Cu : Cursor := First (S1);
   begin
      while Has_Element (S1, Cu) loop
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (S1), Cu) - 1 =>
              not Contains (Model (S2), K.Get (Keys (S1), I)));
         if Contains (S2, Key (S1, Cu)) then
            return False;
         end if;
         Cu := Next (S1, Cu);
      end loop;
      return True;
   end Are_Disjoint;

   procedure Union_Prop (S1 : in out Map; S2 : Map) is
      Cu : Cursor := First (S2);
   begin
      while Has_Element (S2, Cu) loop
         pragma Loop_Invariant
           (Length (S1) < Length (S1)'Loop_Entry + P.Get (Positions (S2), Cu));
         pragma Loop_Invariant
           (for all K of S1 => Prop (Element (Model (S1), K)));
         Include (S1, Key (S2, Cu), Element (S2, Cu));
         Cu := Next (S2, Cu);
      end loop;
   end Union_Prop;

   procedure Insert_Count (M : in out Map) is
   begin
      Insert (M, 1, 0);
      Insert (M, 2, 0);
      Insert (M, 3, 0);
      Insert (M, 4, 0);
   end Insert_Count;

   function Q (E : Integer) return Boolean is
   begin
      return E >= 0;
   end Q;

   procedure From_Keys_To_Model (S : Map) is null;

   procedure From_Model_To_Keys (S : Map) is null;

   procedure From_Keys_To_Cursors (S : Map) is null;

   procedure From_Cursors_To_Keys (S : Map) is
   begin
      Lift_Abstraction_Level (S);
   end From_Cursors_To_Keys;

   procedure From_Model_To_Cursors (S : Map) is null;

   procedure From_Cursors_To_Model (S : Map) is
   begin
      Lift_Abstraction_Level (S);
   end From_Cursors_To_Model;

end Use_Ordered_Maps;
