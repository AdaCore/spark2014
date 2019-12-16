with Ada.Unchecked_Deallocation;

package body Formal_Vectors with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   Min_Size : constant := 100;

   function New_Size (Size : Natural) return Natural with
     Post => New_Size'Result >= Size;

   function New_Size (Size : Natural) return Natural is
   begin
      return
        (if Size < Min_Size / 3 then Min_Size
         elsif Size > Natural'Last / 3 then Natural'Last
         else Size * 3);
   end New_Size;

   function Size (V : Vector) return Natural is
     (if V.Content = null then 0
      else V.Content.all'Length);

   procedure Free is new Ada.Unchecked_Deallocation
     (Element_Array, Element_Array_Access);

   procedure Free is new Ada.Unchecked_Deallocation
     (Element_Type, Element_Access);

   procedure Resize (V : in out Vector; Min_Size : Natural := 0) with
     Post => Size (V) >= Min_Size
       and then Size (V) >= Size (V)'Old
       and then
         (if Size (V)'Old < Natural'Last
          and then Min_Size = 0 then Size (V) > V.Top)
       and then V.Top = V.Top'Old
       and then Model (V) = Model (V)'Old
   is
      S : constant Natural :=
        (if V.Top /= Natural'Last and then Min_Size = 0
         then V.Top + 1 else Min_Size);
      NS : constant Natural := New_Size (S);
   begin
      if V.Content = null then
         V.Content := new Element_Array (1 .. NS);
      elsif S <= V.Content'Length then
         return;
      else
         declare
            New_Content : Element_Array_Access :=
              new Element_Array (1 .. NS);
            Old_Content : Element_Array_Access := V.Content;
         begin
            New_Content.all (1 .. Old_Content.all'Length) := Old_Content.all;
            V.Content := New_Content;
            --  Free (Old_Content); free of write only object not supported by borrow checker yet
         end;
      end if;
   end Resize;

   procedure Move (From, To : in out Element_Access) with
   --  Something strange happens with inlining of Move, remove contract to see
     Pre  => From /= null,
     Post => To /= null and then Model(To.all) = Model(From.all)'Old and then From = null
   is
   begin
      Free (To);
      To := From;
      From := null;
   end Move;

   procedure Swap (From, To : in out Element_Access) with
     Pre  => From /= null and then To /= null,
     Post => From /= null and then To /= null and then Model(To.all) = Model(From.all)'Old and then Model(From.all) = Model(To.all)'Old
   is
      Tmp : Element_Access := To;
   begin
      To := From;
      From := Tmp;
   end Swap;

   procedure Append (V : in out Vector; E : Element_Type) is
   begin
      Resize (V);
      V.Content (V.Top + 1) := new Element_Type'(Copy (E));
      V.Top := V.Top + 1;
   end Append;

   procedure Append (V : in out Vector; E : in out Vector) is
      E_Top : constant Natural := E.Top;
      E_Mod : constant Model_Type := Model (E) with Ghost;
      V_Mod : constant Model_Type := Model (V) with Ghost;
   begin
      if E.Top = 0 then
         return;
      end if;

      Resize (V, V.Top + E.Top);
      E.Top := 0;
      for I in 1 .. E_Top loop
         --  ??? restore generation of frame condition for access
         pragma Loop_Invariant (E.Content /= null);
         pragma Loop_Invariant (E.Content'Length >= E_Top);
         pragma Loop_Invariant
           (for all J in I .. E_Top => E.Content (J) /= null);
         pragma Loop_Invariant
           (for all J in I .. E_Top => Model (E.Content (J).all) = Get (E_Mod, J));
         pragma Loop_Invariant (V.Content /= null);
         pragma Loop_Invariant
           (for all J in 1 .. V.Top =>
              Model (V.Content (J).all) = Get (V_Mod, J));
         pragma Loop_Invariant (V.Content'Length >= V.Top + E_Top);
         pragma Loop_Invariant
           (for all J in V.Top + 1 .. V.Top + I - 1 => V.Content (J) /= null
            and then
              Model (V.Content (J).all) = Get (E_Mod, J - V.Top));
         Move (To => V.Content (V.Top + I), From => E.Content (I));
      end loop;
      V.Top := V.Top + E_Top;
   end Append;

   procedure Insert (V : in out Vector; I : Positive; E : Element_Type) is
      V_Mod : constant Model_Type := Model (V) with Ghost;
      X : Element_Access := new Element_Type'(Copy (E));
   begin
      Resize (V);
      for J in I .. V.Top loop
         pragma Loop_Invariant (V.Content /= null);
         pragma Loop_Invariant (V.Content'Length > Last (V_Mod));
         pragma Loop_Invariant
           (for all J in 1 .. V.Top => V.Content (J) /= null);
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 =>
              Model (V.Content (J).all) = Get (V_Mod, J));
         pragma Loop_Invariant (X /= null);
         pragma Loop_Invariant
           (if J > I then Model (V.Content (I).all) = Model (E) and then Model (X.all) = Get (V_Mod, J - 1)
            else X.all = E);
         pragma Loop_Invariant
           (for all K in I + 1 .. J - 1 =>
              Model (V.Content (K).all) = Get (V_Mod, K - 1));
         pragma Loop_Invariant
           (for all K in J .. V.Top =>
              Model (V.Content (K).all) = Get (V_Mod, K));
         Swap (V.Content (J), X);
      end loop;
      V.Content (V.Top + 1) := X;
      V.Top := V.Top + 1;
   end Insert;

   procedure Replace (V : in out Vector; I : Positive; E : Element_Type) is
   begin
      V.Content (I).all := Copy (E);
   end Replace;

   procedure Delete_Last (V : in out Vector) is
   begin
      if V.Top > 0 then
         V.Top := V.Top - 1;
      end if;
   end Delete_Last;

   procedure Delete (V : in out Vector; I : Positive) is
      V_Mod : constant Model_Type := Model (V) with Ghost;
   begin
      if V.Top > 0 then
         V.Top := V.Top - 1;
         for J in I .. V.Top loop
            pragma Loop_Invariant (V.Content /= null);
            pragma Loop_Invariant (V.Content'Length >= Last (V_Mod));
            pragma Loop_Invariant
              (for all J in 1 .. V.Top + 1 =>
                 V.Content (J) /= null);
            pragma Loop_Invariant
              (for all J in 1 .. I - 1 =>
                 Model (V.Content (J).all) = Get (V_Mod, J));
            pragma Loop_Invariant
              (for all K in I .. J - 1 =>
                 Model (V.Content (K).all) = Get (V_Mod, K + 1));
            pragma Loop_Invariant
              (for all K in J + 1 .. V.Top + 1 =>
                 Model (V.Content (K).all) = Get (V_Mod, K));
            Swap (V.Content (J), V.Content (J + 1));
         end loop;
         Free (V.Content (V.Top + 1));
      end if;
   end Delete;

   function Element (V : Vector; I : Positive) return Element_Type is
     (Copy (V.Content (I).all)) with SPARK_Mode => Off;

   -- function Element (V : Vector; I : Positive) return access Element_Type is
   --   (V.Content (I));

   function Model (V : Vector) return Model_Type with
     Refined_Post => Last (Model'Result) = V.Top
     and then (for all I in 1 .. V.Top => Get (Model'Result, I) = Model (V.Content (I).all))
   is
      M : Model_Type;
   begin
      for I in 1 .. V.Top loop
         pragma Loop_Invariant (Last (M) = I - 1);
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 => Get (M, J) = Model (V.Content (J).all));
         M := Add (M, Model (V.Content (I).all));
      end loop;
      return M;
   end Model;
end Formal_Vectors;
