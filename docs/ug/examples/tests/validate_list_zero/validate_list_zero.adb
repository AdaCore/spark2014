with Loop_Types; use Loop_Types; use Loop_Types.Lists;
with Ada.Containers; use Ada.Containers; use Loop_Types.Lists.Formal_Model;

procedure Validate_List_Zero (L : List_T; Success : out Boolean) with
  SPARK_Mode,
  Post => Success = (for all E of L => E = 0)
is
   Cu : Cursor := First (L);
begin
   while Has_Element (L, Cu) loop
      pragma Loop_Invariant (for all I in 1 .. P.Get (Positions (L), Cu) - 1 =>
                               Element (Model (L), I) = 0);
      if Element (L, Cu) /= 0 then
         Success := False;
         return;
      end if;
      Next (L, Cu);
   end loop;

   Success := True;
end Validate_List_Zero;
