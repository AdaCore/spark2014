with Loop_Types; use Loop_Types; use Loop_Types.Lists;
with Ada.Containers; use Ada.Containers; use Loop_Types.Lists.Formal_Model;

procedure Update_Range_List_Zero (L : in out List_T; First, Last : Cursor) with
  SPARK_Mode,
  Pre  => Has_Element (L, First) and then Has_Element (L, Last)
  and then P.Get (Positions (L), First) <= P.Get (Positions (L), Last),
  Post => Length (L) = Length (L)'Old
  and Positions (L) = Positions (L)'Old
  and (for all I in 1 .. Length (L) =>
            (if I in P.Get (Positions (L), First) .. P.Get (Positions (L), Last) then
               Element (Model (L), I) = 0
             else Element (Model (L), I) = Element (Model (L'Old), I)))
is
   Cu : Cursor := First;
begin
   loop
      pragma Loop_Invariant (Has_Element (L, Cu));
      pragma Loop_Invariant (P.Get (Positions (L), Cu) in P.Get (Positions (L), First) .. P.Get (Positions (L), Last));
      pragma Loop_Invariant (Length (L) = Length (L)'Loop_Entry);
      pragma Loop_Invariant (Positions (L) = Positions (L)'Loop_Entry);
      pragma Loop_Invariant (for all I in 1 .. Length (L) =>
                               (if I in P.Get (Positions (L), First) .. P.Get (Positions (L), Cu) - 1 then
                                   Element (Model (L), I) = 0
                                else Element (Model (L), I) = Element (Model (L'Loop_Entry), I)));
      Replace_Element (L, Cu, 0);
      exit when Cu = Last;
      Next (L, Cu);
   end loop;
end Update_Range_List_Zero;
