pragma Ada_2012;
with Ada.Containers.Formal_Indefinite_Vectors;
with Ada.Containers; use Ada.Containers;

package Use_Vectors with SPARK_Mode is
   package Nested is
      function Id (X, F, L : Integer) return Integer
        with Post => (if X in F .. L then Id'Result in F .. L);
      pragma Annotate (GNATprove, Terminating, Id);
   private
      pragma SPARK_Mode (Off);
      function Id (X, F, L : Integer) return Integer is (X);
   end Nested;

   subtype Smaller is Integer range Integer'First + 1 .. Integer'Last;
   Fst : constant Smaller := Nested.Id (1, Integer'First + 1, Integer'Last);
   subtype Bigger is Integer range Fst .. Integer'Last;
   Lst : constant Bigger := Nested.Id (Integer'Last, Fst, Integer'Last);

   subtype Index_Type is Integer range Fst .. Lst;

   type Element_Type is new Integer;
   package My_Vectors is new Ada.Containers.Formal_Indefinite_Vectors
       (Index_Type   => Index_Type,
        Element_Type => Element_Type,
        Bounded      => False,
        Max_Size_In_Storage_Elements => Element_Type'Size);

   use My_Vectors;
   use My_Vectors.Formal_Model;

   pragma Unevaluated_Use_Of_Old (Allow);

   function Is_Incr (I1, I2 : Element_Type) return Boolean is
      (if I1 = Element_Type'Last then I2 = Element_Type'Last else I2 = I1 + 1);

   procedure Incr_All (V1 : Vector; V2 : in out Vector) with
     Post => Length (V2) = Length (V1)
     and (for all N in Index_Type'First .. Last_Index (V1) =>
              Is_Incr (Element (V1, N), Element (V2, N)));
   --  Loop through a vector to increment each element. Store the incremented
   --  elements in V2.

   procedure Incr_All_2 (V : in out Vector) with
     Post => Length (V) = Length (V)'Old
     and (for all N in Index_Type'First .. Last_Index (V) =>
              Is_Incr (Element (Model (V)'Old, N),
                       Element (V, N)));
   --  Same as before except that elements are stored back in V.

   procedure Double_Size (V : in out Vector) with
     Pre  => Capacity (V) / 2 >= Length (V),
     Post => Length (V) = 2 * Length (V)'Old
     and (for all I in Index_Type'First .. Last_Index (V)'Old =>
       Element (V, I) = Element (Model (V)'Old, I)
       and Element (V, I + Integer (Length (V)'Old)) =
           Element (Model (V)'Old, I));
   --  Double the size of list by duplicating every element. New elements are
   --  appended to the list.

   function My_Find (V : Vector; E : Element_Type) return Index_Type'Base
   --  Iterate to find an element E in V.

   with
     Contract_Cases =>
       ((for all I in Index_Type'First .. Last_Index (V) =>
          Element (V, I) /= E) =>
            My_Find'Result = Index_Type'First - 1,
        others => My_Find'Result in Index_Type'First .. Last_Index (V)
        and then Element (V, My_Find'Result) = E
        and then (for all I in Index_Type'First .. My_Find'Result - 1 =>
                  Element (V, I) /= E));

   procedure Update_Range_To_Zero (V : in out Vector; Fst, Lst : Index_Type)
   --  Replace every element between Fst and Lst with 0.

   with
     Pre  => Lst <= Last_Index (V) and then Fst <= Lst,
     Post => (for all I in Index_Type'First .. Last_Index (V) =>
              (if I in Fst .. Lst
               then Element (V, I) = 0
               else Element (V, I) = Element (Model (V)'Old, I)));

   Count : constant := 7;

   procedure Insert_Count (V : in out Vector; I : Index_Type)
   --  Insert 0 Count times just before I.

   with
     Pre  => I <= Last_Index (V) and Capacity (V) - Count >= Length (V),
     Post => Length (V) = Length (V)'Old + Count
     and (for all J in Index_Type'First .. I - 1 =>
        Element (V, J) = Element (Model (V)'Old, J))
     and (for all J in I .. I + Count - 1 => Element (V, J) = 0)
     and (for all J in I + Count .. Last_Index (V) =>
              Element (V, J) = Element (Model (V)'Old, J - Count));
end Use_Vectors;
