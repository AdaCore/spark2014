with Loop_Types; use Loop_Types; use Loop_Types.Lists;
with Ada.Containers; use Ada.Containers; use Loop_Types.Lists.Formal_Model;

procedure Search_List_Zero (L : List_T; Pos : out Cursor; Success : out Boolean) with
  SPARK_Mode,
  Post => Success = (for some E of L => E = 0) and then
          (if Success then Element (L, Pos) = 0)
is
   Cu : Cursor := First (L);
begin
   while Has_Element (L, Cu) loop
      pragma Loop_Invariant (for all I in 1 .. P.Get (Positions (L), Cu) - 1 =>
                               Element (Model (L), I) /= 0);
      if Element (L, Cu) = 0 then
         Success := True;
         Pos := Cu;
         return;
      end if;
      Next (L, Cu);
   end loop;

   Success := False;
   Pos := No_Element;
end Search_List_Zero;
