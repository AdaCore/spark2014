with Types;               use Types;
with Pair_Insertion_Sort; use Pair_Insertion_Sort;
with Ada.Text_IO;         use Ada.Text_IO;

procedure Test_Sort with
  SPARK_Mode => Off
is
   A : Arr := (10, 8, 6, 3, 4, 1, 9, 7, 2, 5);
begin
   Sort (A);
   Put ("A = (");
   for I in A'Range loop
      Put (Integer'Image (A(I)) & ',');
   end loop;
   Put_Line (")");
end Test_Sort;
