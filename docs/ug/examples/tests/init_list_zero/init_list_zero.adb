with Loop_Types; use Loop_Types; use Loop_Types.Lists;
with Ada.Containers; use Ada.Containers; use Loop_Types.Lists.Formal_Model;

procedure Init_List_Zero (L : in out List_T) with
  SPARK_Mode,
  Post => (for all E of L => E = 0)
is
   Cu : Cursor := First (L);
begin
   while Has_Element (L, Cu) loop
      pragma Loop_Invariant (for all I in 1 .. P.Get (Positions (L), Cu) - 1 =>
                               Element (Model (L), I) = 0);
      Replace_Element (L, Cu, 0);
      Next (L, Cu);
   end loop;
end Init_List_Zero;
