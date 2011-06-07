with Simple_Unc_Arrays; use Simple_Unc_Arrays;
with Ada.Text_IO; use Ada.Text_IO;

procedure My_Test is

   T1 : Table := (10, (5, 1, 3, 0, 9, 8, 2, 7, 4, 6));
   T2 : Table := (10, (4, 8, 6, 9, 0, 1, 7, 2, 5, 3));

   T3 : Table (10);

begin
   Put_Line ("Max = " & Max (T1)'img);
   Put_Line ("Min = " & Min (T1)'img );
   Put_Line ("Average = " & Average (T1)'img);
   Put_Line ("Find 0 in T1 " & Search (T1, 0)'img);
   Put_Line ("Find 9 in T2 " & Search (T2, 9)'img);

   T3 := Add (T1, T2);
   pragma Assert (for all I in 1 .. T3.Last => T3.V (I) = 9);

   T3 := Bubble_Sort (T1);
   Quick_Sort (T1);
   pragma Assert (T1 = T3);
end;
