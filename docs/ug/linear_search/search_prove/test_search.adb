with Search;      use Search;
with Ada.Text_IO; use Ada.Text_IO;

procedure Test_Search is
   A     : constant Arr := (1, 5, 3, 8, 8, 2, 0, 1, 0, 4);
   Idx   : Index;
   Found : Boolean;
   
begin
   Found := Linear_Search (A, 0, Idx);
   if Found then
      if Idx = 7 then
         Put_Line ("OK: Found existing value at first index");
      else
         Put_Line ("not OK: Found existing value at other index");
      end if;
   else
      Put_Line ("not OK: Did not find existing value");
   end if;
   
   Found := Linear_Search (A, 6, Idx);
   if not Found then
      Put_Line ("OK: Did not find non-existing value");
   else
      Put_Line ("not OK: Found non-existing value");
   end if;
end Test_Search;
     
     
     
