pragma Unevaluated_Use_Of_Old (Allow);
with Loop_Types; use Loop_Types; use Loop_Types.Vectors;
use Loop_Types.Vectors.Formal_Model;

procedure Update_Range_Vec_Zero (V : in out Vec_T; First, Last : Index_T) with
  SPARK_Mode,
  Pre  => Last <= Last_Index (V),
  Post => (for all J in 1 .. Last_Index (V) =>
               (if J in First .. Last then Element (V, J) = 0
                else Element (V, J) = Element (Model (V)'Old, J)))
is
begin
   for J in First .. Last loop
      Replace_Element (V, J, 0);
      pragma Loop_Invariant (Last_Index (V) = Last_Index (V)'Loop_Entry);
      pragma Loop_Invariant
        (for all I in 1 .. Last_Index (V) =>
               (if I in First .. J then Element (V, I) = 0
                else Element (V, I) = Element (Model (V)'Loop_Entry, I)));
   end loop;
end Update_Range_Vec_Zero;
