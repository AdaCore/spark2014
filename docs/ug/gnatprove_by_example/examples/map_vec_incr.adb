pragma Unevaluated_Use_Of_Old (Allow);
with Loop_Types; use Loop_Types; use Loop_Types.Vectors;
use Loop_Types.Vectors.Formal_Model;

procedure Map_Vec_Incr (V : in out Vec_T) with
  SPARK_Mode,
  Pre  => (for all I in 1 .. Last_Index (V) =>
               Element (V, I) /= Component_T'Last),
  Post => Last_Index (V) = Last_Index (V)'Old
  and then (for all I in 1 .. Last_Index (V) =>
                 Element (V, I) = Element (Model (V)'Old, I) + 1)
is
begin
   for J in 1 .. Last_Index (V) loop
      pragma Loop_Invariant (Last_Index (V) = Last_Index (V)'Loop_Entry);
      pragma Loop_Invariant
        (for all I in 1 .. J - 1 =>
           Element (V, I) = Element (Model (V)'Loop_Entry, I) + 1);
      pragma Loop_Invariant
        (for all I in J .. Last_Index (V) =>
           Element (V, I) = Element (Model (V)'Loop_Entry, I));
      Replace_Element (V, J, Element (V, J) + 1);
   end loop;
end Map_Vec_Incr;
