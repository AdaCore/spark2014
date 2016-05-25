with Loop_Types; use Loop_Types; use Loop_Types.Lists;

procedure Map_List_Incr (L : in out List_T) with
  SPARK_Mode,
  Pre  => (for all E of L => E /= Component_T'Last),
  Post => (for all Cu in L =>
             Has_Element (L'Old, Cu) and then
             Element (L, Cu) = Element (L'Old, Cu) + 1)
is
   Cu : Cursor := First (L);
begin
   while Has_Element (L, Cu) loop
      pragma Loop_Invariant (for all Cu2 in First_To_Previous (L, Cu) => Has_Element (L'Loop_Entry, Cu2));
      pragma Loop_Invariant (for all Cu2 in First_To_Previous (L, Cu) => Element (L, Cu2) = Element (L'Loop_Entry, Cu2) + 1);
      pragma Loop_Invariant (for all Cu2 in Current_To_Last (L, Cu) => Element (L, Cu2) = Element (L'Loop_Entry, Cu2));
      pragma Loop_Invariant (Strict_Equal (Current_To_Last (L'Loop_Entry, Cu), Current_To_Last (L, Cu)));
      pragma Loop_Invariant (Has_Element (L'Loop_Entry, Cu));
      Replace_Element (L, Cu, Element (L, Cu) + 1);
      Next (L, Cu);
   end loop;
end Map_List_Incr;
