with Binary_Search; use Binary_Search;
with Ada.Text_IO;   use Ada.Text_IO;

procedure Test_Search is
   A   : constant Ar := (0, 0, 1, 1, 3, 4, 5, 8, 8, others => 10);
   B   : constant Ar := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
   Res : T;
begin
   Res := Search (A, 1);
   if Res /= 0 then
      if Res = 3 then
         Put_Line ("OK: Found existing value at first index");
      else
         Put_Line ("not OK: Found existing value at other index");
      end if;
   else
      Put_Line ("not OK: Did not find existing value");
   end if;

   Res := Search (A, 6);
   if Res = 0 then
      Put_Line ("OK: Did not find non-existing value");
   else
      Put_Line ("not OK: Found non-existing value");
   end if;

   Res := Search (B, 2);
   if Res /= 0 then
      if Res = 2 then
         Put_Line ("OK: Found existing value at first index");
      else
         Put_Line ("not OK: Found existing value at other index");
      end if;
   else
      Put_Line ("not OK: Did not find existing value");
   end if;
end Test_Search;
