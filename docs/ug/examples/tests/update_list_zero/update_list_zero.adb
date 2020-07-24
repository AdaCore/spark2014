with Loop_Types; use Loop_Types; use Loop_Types.Lists;
with Ada.Containers; use Ada.Containers; use Loop_Types.Lists.Formal_Model;

procedure Update_List_Zero (L : in out List_T; Threshold : Component_T) with
  SPARK_Mode,
  Post => Length (L) = Length (L)'Old
  and (for all I in 1 .. Length (L) =>
            Element (Model (L), I) =
             (if Element (Model (L'Old), I) <= Threshold then 0
              else Element (Model (L'Old), I)))
is
   Cu : Cursor := First (L);
begin
   while Has_Element (L, Cu) loop
      pragma Loop_Invariant (Length (L) = Length (L)'Loop_Entry);
      pragma Loop_Invariant
        (for all I in 1 .. P.Get (Positions (L), Cu) - 1 =>
            Element (Model (L), I) =
             (if Element (Model (L'Loop_Entry), I) <= Threshold then 0
              else Element (Model (L'Loop_Entry), I)));
      pragma Loop_Invariant
        (for all I in P.Get (Positions (L), Cu) .. Length (L) =>
            Element (Model (L), I) = Element (Model (L'Loop_Entry), I));
      if Element (L, Cu) <= Threshold then
         Replace_Element (L, Cu, 0);
      end if;
      Next (L, Cu);
   end loop;
end Update_List_Zero;
