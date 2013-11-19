with Simple_Unc_Arrays; use Simple_Unc_Arrays;

procedure My_Test is pragma SPARK_Mode (On);

   T1 : Table := (10, (5, 1, 3, 0, 9, 8, 2, 7, 4, 6));
   T2 : Table := (10, (4, 8, 6, 9, 0, 1, 7, 2, 5, 3));

   T3 : Table (10);

begin
   Output ("Max = ", Max (T1));
   Output ("Min = ", Min (T1));
   Output ("Average = ", Average (T1));
   Output ("Find 0 in T1 ", Value (Search (T1, 0)));
   Output ("Find 9 in T2 ", Value (Search (T2, 9)));

   T3 := Add (T1, T2);
   pragma Assert (for all I in 1 .. T3.Last => T3.V (I) = 9);

   T3 := Bubble_Sort (T1);
   Quick_Sort (T1);
   pragma Assert (T1 = T3);
end;
