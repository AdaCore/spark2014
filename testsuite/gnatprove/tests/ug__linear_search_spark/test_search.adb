with Linear_Search; use Linear_Search;
with Ada.Text_IO;   use Ada.Text_IO;

procedure Test_Search is
   A   : constant Arr := (1, 5, 3, 8, 8, 2, 0, 1, 0, 4);
   Res : Search_Result;

begin
   Res := Search (A, 1);
   if Res.Found then
      if Res.At_Index = 1 then
         Put_Line ("OK: Found existing value at first index");
      else
         Put_Line ("not OK: Found existing value at other index");
      end if;
   else
      Put_Line ("not OK: Did not find existing value");
   end if;

   Res := Search (A, 6);
   if not Res.Found then
      Put_Line ("OK: Did not find non-existing value");
   else
      Put_Line ("not OK: Found non-existing value");
   end if;
end Test_Search;



