pragma SPARK_Mode(Off);
with List; use List;
with Text_IO; use Text_IO;
procedure Main is

   L : List.List;

begin
   for I in 1 .. 10 loop
      Append (L, I);
   end loop;

   declare
      Rev_L : List.List := Reverse_List (L);
   begin
      for I in 1 .. 10 loop
         Put_Line (Element (Rev_L, I)'img);
      end loop;
   end;
end main;
