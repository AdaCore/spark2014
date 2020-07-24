pragma Unevaluated_Use_Of_Old (Allow);
with Loop_Types; use Loop_Types; use Loop_Types.Vectors;
use Loop_Types.Vectors.Formal_Model;

procedure Update_Vec_Zero (V : in out Vec_T; Threshold : Component_T) with
  SPARK_Mode,
  Post => Last_Index (V) = Last_Index (V)'Old
  and (for all I in 1 .. Last_Index (V) =>
            Element (V, I) =
             (if Element (Model (V)'Old, I) <= Threshold then 0
              else Element (Model (V)'Old, I)))
is
begin
   for J in First_Index (V) .. Last_Index (V) loop
      pragma Loop_Invariant (Last_Index (V) = Last_Index (V)'Loop_Entry);
      pragma Loop_Invariant
        (for all I in 1 .. J - 1 =>
             Element (V, I) =
              (if Element (Model (V)'Loop_Entry, I) <= Threshold then 0
               else Element (Model (V)'Loop_Entry, I)));
      pragma Loop_Invariant
        (for all I in J .. Last_Index (V) =>
             Element (V, I) = Element (Model (V)'Loop_Entry, I));
      if Element (V, J) <= Threshold then
         Replace_Element (V, J, 0);
      end if;
   end loop;
end Update_Vec_Zero;
