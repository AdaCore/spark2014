with Loop_Types; use Loop_Types; use Loop_Types.Lists;

procedure Update_Range_List_Zero (L : in out List_T; First, Last : Cursor) with
  SPARK_Mode,
  Pre  => Has_Element (L, First) and then Has_Element (Current_To_Last (L, First), Last),
  Post => (for all Cu in Current_To_Last (First_To_Previous (L, Next (L, Last)), First) => Element (L, Cu) = 0)
    and (for all Cu2 in First_To_Previous (L, First) => Has_Element (L'Old, Cu2) and then Element (L, Cu2) = Element (L'Old, Cu2))
    and (for all Cu2 in Current_To_Last (L, Next (L, Last)) => Has_Element (L'Old, Cu2) and then Element (L, Cu2) = Element (L'Old, Cu2))
is
   Cu : Cursor := First;
begin
   loop
      pragma Loop_Invariant ((if Cu /= First then Has_Element (First_To_Previous (L, Cu), First)) and Has_Element (L, Cu) and Has_Element (L'Loop_Entry, Cu) and Has_Element (Current_To_Last (L, Cu), Last));
      pragma Loop_Invariant (if Cu /= First then (for all Cu2 in Current_To_Last (First_To_Previous (L, Cu), First) => Element (L, Cu2) = 0));
      pragma Loop_Invariant (for all Cu2 in First_To_Previous (L, First) => Has_Element (L'Loop_Entry, Cu2) and then Element (L, Cu2) = Element (L'Loop_Entry, Cu2));
      pragma Loop_Invariant (Strict_Equal (Current_To_Last (L, Cu), Current_To_Last (L'Loop_Entry, Cu)));
      Replace_Element (L, Cu, 0);
      exit when Cu = Last;
      Next (L, Cu);
   end loop;
end Update_Range_List_Zero;
