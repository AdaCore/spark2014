pragma Ada_2012;

package body Use_Vectors with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   procedure Incr_All (V1 : Vector; V2 : in out Vector) is
      Lst : Index_Type'Base := Last_Index (V1);
   begin
      Clear (V2);
      for I in Index_Type'First .. Lst loop
         pragma Loop_Invariant (Integer (Length (V2)) = I - Index_Type'First);
         pragma Loop_Invariant
           (for all N in Index_Type'First .. Last_Index (V2) =>
                Is_Incr (Element (V1, N), Element (V2, N)));
         if Element (V1, I) < Element_Type'Last then
            Append (V2, Element (V1, I) + 1);
         else
            Append (V2, Element (V1, I));
         end if;
      end loop;
   end Incr_All;

   procedure Incr_All_2 (V : in out Vector) is
      Lst : Index_Type'Base := Last_Index (V);
   begin
      for I in Index_Type'First .. Lst loop
         pragma Loop_Invariant (Length (V) = Length (V)'Loop_Entry);
         pragma Loop_Invariant
           (for all N in Index_Type'First .. I - 1 =>
                Is_Incr (Element (Model (V)'Loop_Entry, N),
                         Element (V, N)));
         pragma Loop_Invariant
           (for all N in I .. Last_Index (V) =>
                Element (Model (V)'Loop_Entry, N) =
                Element (V, N));
         if Element (V, I) < Element_Type'Last then
            Replace_Element (V, I, Element (V, I) + 1);
         end if;
      end loop;
   end Incr_All_2;

   procedure Double_Size (V : in out Vector) is
      Lst : Index_Type'Base := Last_Index (V);
   begin
      for I in Index_Type'First .. Lst loop
         pragma Loop_Invariant
           (Integer (Length (V)) =
            Integer (Length (V)'Loop_Entry) + (I - Index_Type'First));
         pragma Loop_Invariant
           (for all J in Index_Type'First .. Last_Index (V)'Loop_Entry =>
              Element (V, J) = Element (Model (V)'Loop_Entry, J));
         pragma Loop_Invariant
           (for all J in Index_Type'First .. I - 1 =>
              Element (V, J + Integer (Length (V)'Loop_Entry)) =
                Element (Model (V)'Loop_Entry, J));
         Append (V, Element (V, I));
      end loop;
   end Double_Size;

   function My_Find (V : Vector; E : Element_Type) return Index_Type'Base is
      Lst : Index_Type'Base := Last_Index (V);
   begin
      for Current in Index_Type'First .. Lst loop
         pragma Loop_Invariant
           (for all I in Index_Type'First .. Current - 1 =>
              Element (V, I) /= E);
         if Element (V, Current) = E then
            return Current;
         end if;
      end loop;
      return Index_Type'First - 1;
   end My_Find;

   procedure Update_Range_To_Zero (V : in out Vector; Fst, Lst : Index_Type) is
   begin
      for Current in Fst .. Lst loop
         pragma Loop_Invariant (Length (V) = Length (V)'Loop_Entry);
         pragma Loop_Invariant
           (for all I in Fst .. Current - 1 =>
                Element (V, I) = 0);
         pragma Loop_Invariant
           (for all I in Index_Type'First .. Fst - 1 =>
              Element (V, I) = Element (Model (V)'Loop_Entry, I));
         pragma Loop_Invariant
           (for all I in Current .. Last_Index (V) =>
                Element (V, I) = Element (Model (V)'Loop_Entry, I));
         Replace_Element (V, Current, 0);
      end loop;
   end Update_Range_To_Zero;

   procedure Insert_Count (V : in out Vector; I : Index_Type) is
   begin
      Insert (V, I, 0);
      Insert (V, I, 0);
      Insert (V, I, 0);
      Insert (V, I, 0);
      Insert (V, I, 0);
      Insert (V, I, 0);
      Insert (V, I, 0);
   end Insert_Count;

end Use_Vectors;
