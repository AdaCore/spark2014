with List; use List;
with Text_IO; use Text_IO;
procedure Main is

   L : List.List;

begin
   for I in 1 .. 10 loop
      My_Lists.Append (L, I);
   end loop;

   L:= Reverse_List (L);

   for I in 1 .. 10 loop
      Put_Line (My_Lists.Element (L, I)'img);
   end loop;
 end main;
