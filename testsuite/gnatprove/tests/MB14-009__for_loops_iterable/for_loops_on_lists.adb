package body For_Loops_On_Lists with SPARK_Mode is

   function Search_0_For_In (L : List) return Cursor is
   begin
      for Cu in L loop
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (L), Cu) - 1 =>
              Element (Model (L), I) /= 0);
         if Element (L, Cu) = 0 then
            return Cu;
         end if;
      end loop;
      return No_Element;
   end Search_0_For_In;

   function Contains_0_For_Of (L : List) return Boolean is
   begin
      for E of L loop
         if E = 0 then
            return True;
         end if;
      end loop;
      return False;
   end Contains_0_For_Of;

   procedure Search_For_In (L : in out List; C : out Cursor) is
   begin
      for Cu in L loop
         if Element (L, Cu) = 0 then
            C := Cu;
            return;
         end if;

         pragma Loop_Invariant (Length (L) = Length (L'Loop_Entry));
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (L), Cu) - 1 =>
              Element (Model (L'Loop_Entry), I) > 0
            and then Element (Model (L), I)
                   = Element (Model (L'Loop_Entry), I) - 1);
         pragma Loop_Invariant
           (for all I in P.Get (Positions (L), Cu) .. Length (L) =>
                Element (Model (L), I)
              = Element (Model (L'Loop_Entry), I));
         pragma Loop_Invariant (Element (L, Cu) /= 0);

         Replace_Element (L, Cu, Element (L, Cu) - 1);
      end loop;
      C := No_Element;
   end Search_For_In;

   function Count_For_Of (L : List) return Boolean is
      Count_0 : Natural := 0;
      Count_1 : Natural := 0;
   begin
      for E of L loop
         if E = 0 then
            Count_0 := Count_0 + 1;
         end if;
         pragma Loop_Invariant
           (if Count_0 > 0 then (for some Cu in L => Element (L, Cu) = 0));
         pragma Loop_Invariant
           (if Count_1 > 0 then (for some Cu in L => Element (L, Cu) = 1));
         if E = 1 then
            Count_1 := Count_1 + 1;
         end if;
      end loop;
      return Count_1 > 0 and then Count_0 > 0;
   end Count_For_Of;
end For_Loops_On_Lists;
