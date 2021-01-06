with List; use List;
with Print;
procedure Main is pragma SPARK_Mode (On);

   L : List.List;

begin
   for I in 1 .. 10 loop
      My_Lists.Append (L, I);
   end loop;

   declare
      Rev_L : List.List := Reverse_List (L);
   begin
      for I in 1 .. 10 loop
         Print.Put (My_Lists.Element (Rev_L, I));
      end loop;
   end;
end main;
