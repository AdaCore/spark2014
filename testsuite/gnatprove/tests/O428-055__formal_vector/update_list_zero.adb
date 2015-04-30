with Loop_Types; use Loop_Types; use Loop_Types.Lists;

procedure Update_List_Zero (L : in out List_T; Threshold : Component_T) with
  SPARK_Mode,
  Post => (for all Cu in L => Has_Element (L'Old, Cu) and then
               Element (L, Cu) = (if Element (L'Old, Cu) <= Threshold then 0 else Element (L'Old, Cu)))
is
   Cu : Cursor := First (L);
begin
   while Has_Element (L, Cu) loop
      pragma Loop_Invariant (for all Cu2 in First_To_Previous (L, Cu) =>
                               Has_Element (L'Loop_Entry, Cu2));
      pragma Loop_Invariant (for all Cu2 in First_To_Previous (L, Cu) =>
                               Element (L, Cu2) = (if Element (L'Loop_Entry, Cu2) <= Threshold then 0 else Element (L'Loop_Entry, Cu2)));
      pragma Loop_Invariant (Strict_Equal (Current_To_Last (L'Loop_Entry, Cu), Current_To_Last (L, Cu)));
      pragma Loop_Invariant (Has_Element (L'Loop_Entry, Cu));
      if Element (L, Cu) <= Threshold then
         Replace_Element (L, Cu, 0);
      end if;
      Next (L, Cu);
   end loop;
end Update_List_Zero;
